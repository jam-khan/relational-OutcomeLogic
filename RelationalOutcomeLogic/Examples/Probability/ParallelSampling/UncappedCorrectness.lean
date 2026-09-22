import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Correctness
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.Limits
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.Limits

/-!
# Population correctness and termination of the actual uncapped collector

A successful prefix of length `m` stays successful after appending fresh jobs.
The window bound ensures its run at cap `m + window` is strictly inside that cap.
This supplies the missing lower bound between reference success approximations
and the increasing interior approximations of the actual event loop.
-/

namespace RelOL.Prob.ParallelSampling
universe u
variable {α : Type u}
noncomputable section

def PoolResult.population (r : PoolResult α) : List α := r.answer.population

private theorem used_le_length (quota : Nat) (jobs : List (Job α)) :
    used quota jobs ≤ jobs.length := by
  induction jobs generalizing quota with
  | nil => cases quota <;> simp [used]
  | cons j jobs ih =>
      cases quota with
      | zero => simp [used]
      | succ n =>
          cases hj : j.accepted <;> simp only [used, hj, Bool.false_eq_true,
            ↓reduceIte, List.length_cons]
          · have := ih (n + 1); omega
          · have := ih n; omega

private theorem successful_prefix_stable (quota : Nat) (xs ys : List (Job α))
    (hs : (select quota xs).succeeded) :
    select quota (xs ++ ys) = select quota xs ∧
      used quota (xs ++ ys) = used quota xs := by
  induction xs generalizing quota with
  | nil =>
      cases quota with
      | zero => simp [select, used]
      | succ n => simp [select, Result.succeeded] at hs
  | cons j xs ih =>
      cases quota with
      | zero => simp [select, used]
      | succ n =>
          cases hj : j.accepted with
          | false =>
              simpa [select, used, hj] using ih (n + 1) (by simpa [select, hj] using hs)
          | true =>
              have htail : (select n xs).succeeded := by
                cases hsel : select n xs <;>
                  simp_all [select, Result.prepend, Result.succeeded]
              obtain ⟨hsel, hused⟩ := ih n htail
              simp [select, used, hj, hsel, hused]

private theorem draws_append (law : Weight (Job α)) (m n : Nat) :
    draws law (m + n) = Weight.bind (draws law m) fun xs =>
      pushforward (fun ys => xs ++ ys) (draws law n) := by
  induction m with
  | zero => simp [draws, pushforward, Weight.bind_pure]
  | succ m ih =>
      rw [Nat.succ_add, draws, ih]
      simp only [draws, pushforward, Weight.bind_assoc, Weight.pure_bind, List.cons_append]

private theorem bind_mono_support {σ τ : Type*} (μ : Weight σ)
    {k l : σ → Weight τ} (h : ∀ s ∈ Weight.support μ, k s ≤ l s) :
    Weight.bind μ k ≤ Weight.bind μ l := by
  intro t
  apply ENNReal.tsum_le_tsum
  intro s
  by_cases hs : μ s = 0
  · simp [hs]
  · exact mul_le_mul' le_rfl (h s hs t)

private theorem prefix_below_interior (workers window quota m : Nat)
    (hw : 0 < workers) (hwindow : 0 < window) (xs ys : List (Job α))
    (hlen : xs.length = m) :
    successValues (select quota xs) ≤
      pushforward PoolResult.population
        (interiorSuccess (m + window) (pool workers window quota (xs ++ ys))) := by
  cases hs : select quota xs with
  | exhausted zs => simp only [successValues]; exact bot_le
  | success zs =>
      have hp := successful_prefix_stable quota xs ys (by simp [hs, Result.succeeded])
      have hu := used_le_length quota xs
      have hstarted := pool_started_le workers window quota hw hwindow (xs ++ ys)
      have hb : (pool workers window quota (xs ++ ys)).started < m + window := by
        rw [hp.2] at hstarted
        omega
      have ha : (pool workers window quota (xs ++ ys)).answer = .success zs :=
        (pool_answer workers window quota hw hwindow _).trans (hp.1.trans hs)
      simp [successValues, interiorSuccess, ha, hb, PoolResult.population,
        Result.population]

/-- Every reference success observed within `m` proposals occurs among the
strictly interior collector executions at cap `m + window`. -/
theorem successful_le_interiorPopulation (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota m : Nat)
    (hw : 0 < workers) (hwindow : 0 < window) :
    successful law m quota ≤ pushforward PoolResult.population
      (interiorCollector law workers window quota (m + window)) := by
  rw [successful_eq_capped, capped_eq_prefix law hlaw, bind_pushforward,
    interiorCollector, freshCollector_eq_scheduledPrefix law hlaw workers window quota
      (m + window) hw hwindow]
  simp only [scheduledPrefix, bind_pushforward, pushforward_bind]
  rw [draws_append, Weight.bind_assoc]
  simp only [bind_pushforward]
  apply bind_mono_support
  intro xs hxs
  have hlen := draws_support_length law m xs hxs
  rw [← Weight.bind_const_of_isProbability (draws law window)
    (draws_probability law hlaw window) (successValues (select quota xs))]
  apply Weight.bind_mono_right
  intro ys
  exact prefix_below_interior workers window quota m hw hwindow xs ys hlen

private theorem interior_population_le_success (cap : Nat) (r : PoolResult α) :
    pushforward PoolResult.population (interiorSuccess cap r) ≤ successValues r.answer := by
  cases ha : r.answer with
  | exhausted xs => simp [interiorSuccess, ha, successValues]
  | success xs =>
      by_cases hc : r.started < cap
      · simp [interiorSuccess, ha, hc, successValues, PoolResult.population, Result.population]
      · simp only [interiorSuccess, ha, if_neg hc, pushforward_zero]; exact bot_le

theorem interiorPopulation_le_successful (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota cap : Nat)
    (hw : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.population (interiorCollector law workers window quota cap) ≤
      successful law cap quota := by
  rw [successful_eq_capped, ← freshCollector_answer law hlaw workers window quota cap hw hwindow,
    bind_pushforward, interiorCollector, pushforward_bind]
  exact Weight.bind_mono_right _ (interior_population_le_success cap)

/-- Complete joint population law of the real uncapped worker-pool loop. This
identity includes subprobability when the acceptance probability is zero. -/
theorem uncappedCollector_population_limit (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota : Nat)
    (hw : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.population (uncappedCollector law workers window quota) =
      successfulLimit law quota := by
  apply le_antisymm
  · rw [uncappedCollector_eq_iSup_interior law workers window quota hw hwindow,
      pushforward_iSup _ _ (interiorCollector_monotone law workers window quota)]
    apply iSup_le
    intro cap
    exact (interiorPopulation_le_successful law hlaw workers window quota cap hw hwindow).trans
      (le_iSup (fun m => successful law m quota) cap)
  · apply iSup_le
    intro m
    exact (successful_le_interiorPopulation law hlaw workers window quota m hw hwindow).trans
      (Weight.bind_mono_left (interiorCollector_le_uncapped law workers window quota (m + window))
        (fun r => Weight.pure r.population))

/-- Positive acceptance gives the same iid accepted conditional population as
sequential rejection sampling, with arbitrary value-dependent finite runtimes. -/
theorem uncappedCollector_population (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law)
    (workers window quota : Nat) (hw : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.population (uncappedCollector law workers window quota) =
      population law quota := by
  rw [uncappedCollector_population_limit law hlaw workers window quota hw hwindow,
    successfulLimit_eq_population law hlaw ha]

private theorem interiorCollector_success (law : Weight (Job α))
    (workers window quota cap : Nat) (r : PoolResult α)
    (hr : r ∈ Weight.support (interiorCollector law workers window quota cap)) :
    r.answer.succeeded := by
  obtain ⟨p, _, hp⟩ := (Weight.mem_support_bind_iff _ _ _).mp hr
  cases ha : p.answer with
  | exhausted xs => simp [interiorSuccess, ha] at hp
  | success xs =>
      by_cases hc : p.started < cap
      · simp only [interiorSuccess, ha, if_pos hc, Weight.support_pure,
          Set.mem_singleton_iff] at hp
        subst r
        simp [ha, Result.succeeded]
      · simp [interiorSuccess, ha, hc] at hp

/-- Every terminating uncapped output is successful, even if total termination
mass is below one. Exhaustion is specific to the finite-cap interface. -/
theorem uncappedCollector_success (law : Weight (Job α)) (workers window quota : Nat)
    (hw : 0 < workers) (hwindow : 0 < window) (r : PoolResult α)
    (hr : r ∈ Weight.support (uncappedCollector law workers window quota)) :
    r.answer.succeeded := by
  have hp : 0 < (⨆ cap, interiorCollector law workers window quota cap) r := by
    rw [← uncappedCollector_eq_iSup_interior law workers window quota hw hwindow]
    exact pos_iff_ne_zero.mpr hr
  simp only [iSup_apply] at hp
  obtain ⟨cap, hcap⟩ := lt_iSup_iff.mp hp
  exact interiorCollector_success law workers window quota cap r hcap.ne'

/-- The success tag and entire ordered population agree with the reference. -/
theorem uncappedCollector_answer (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law)
    (workers window quota : Nat) (hw : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.answer (uncappedCollector law workers window quota) =
      pushforward Result.success (population law quota) := by
  have htag : pushforward PoolResult.answer (uncappedCollector law workers window quota) =
      pushforward (fun r => Result.success r.population)
        (uncappedCollector law workers window quota) := by
    apply Weight.bind_congr_on_support
    intro r hr
    have hs := uncappedCollector_success law workers window quota hw hwindow r hr
    cases he : r.answer with
    | exhausted xs => simp [he, Result.succeeded] at hs
    | success xs => simp [he, PoolResult.population, Result.population]
  rw [htag]
  have h := congrArg (pushforward Result.success)
    (uncappedCollector_population law hlaw ha workers window quota hw hwindow)
  simpa only [pushforward, Weight.bind_assoc, Weight.pure_bind] using h

private theorem population_support_length (law : Weight (Job α)) (quota : Nat)
    (xs : List α) (hx : xs ∈ Weight.support (population law quota)) : xs.length = quota := by
  induction quota generalizing xs with
  | zero =>
      simp only [population, Weight.support_pure, Set.mem_singleton_iff] at hx
      subst xs
      rfl
  | succ n ih =>
      obtain ⟨a, _, ha⟩ := (Weight.mem_support_bind_iff _ _ _).mp hx
      obtain ⟨ys, hy, hys⟩ := (Weight.mem_support_bind_iff _ _ _).mp ha
      simp only [Weight.support_pure, Set.mem_singleton_iff] at hys
      subst xs
      simp only [List.length_cons, ih ys hy]

theorem uncappedCollector_population_length (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law)
    (workers window quota : Nat) (hw : 0 < workers) (hwindow : 0 < window)
    (r : PoolResult α) (hr : r ∈ Weight.support (uncappedCollector law workers window quota)) :
    r.population.length = quota := by
  have hp : r.population ∈ Weight.support
      (pushforward PoolResult.population (uncappedCollector law workers window quota)) := by
    apply (Weight.mem_support_bind_iff _ _ _).mpr
    exact ⟨r, hr, by simp only [Weight.support_pure, Set.mem_singleton_iff]⟩
  rw [uncappedCollector_population law hlaw ha workers window quota hw hwindow] at hp
  exact population_support_length law quota _ hp

/-- An empty requested population terminates immediately, without any assumption
on acceptance, worker capacity, or the job law. -/
theorem uncappedCollector_zero (law : Weight (Job α)) (workers window : Nat) :
    uncappedCollector law workers window 0 =
      Weight.pure ⟨.success [], 0, 0, 0, 0⟩ := by
  have hstop : ¬eventActive workers window false (EventState.initial (α := α) 0 0) := by
    simp [eventActive, eventAction, EventState.initial]
  simp only [uncappedCollector, eventRun, loopSem_neg hstop, pushforward_pure]
  rfl

/-- The actual loop terminates almost surely; this is not a fuel assumption. -/
theorem uncappedCollector_probability (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law)
    (workers window quota : Nat) (hw : 0 < workers) (hwindow : 0 < window) :
    Weight.IsProbability (uncappedCollector law workers window quota) := by
  have h := congrArg Weight.mass
    (uncappedCollector_population law hlaw ha workers window quota hw hwindow)
  rw [mass_pushforward, population_probability law hlaw ha quota] at h
  exact h

end
end RelOL.Prob.ParallelSampling
