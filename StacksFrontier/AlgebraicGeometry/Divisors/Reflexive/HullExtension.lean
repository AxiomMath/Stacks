module

public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionSections
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullCoherentReflexive
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.TorsionSubsheaf.Basic

/-!
# Extending a generic map to the reflexive hull

Let `X` be an integral locally Noetherian normal scheme with generic point `η`, and let `ℱ`, `𝒢`
be coherent `𝒪_X`-modules.  A linear map `T : 𝒢_η ⟶ ℱ_η` of generic stalks extends to a map
`𝒢 ⟶ ℱ^∨∨` of `𝒪_X`-modules if and only if, at every point `x` whose local ring has dimension
one, `T` carries the image of `𝒢_x` into the image of `ℱ_x`.

## Main definitions

* `AlgebraicGeometry.genericStalkModule`: the generic stalk of an `𝒪_X`-module on an integral
  scheme, as a module over the function field.

## Main results

* `AlgebraicGeometry.exists_lift_toReflexiveHull_iff_codimension_one`: the extension criterion.

## References

* [Stacks Project, Tag 0AY7](https://stacks.math.columbia.edu/tag/0AY7)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

/-! ### Surjectivity of the evaluation map in dimension one -/

private theorem dualEval_surjective_of_local_dim_one
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : ringKrullDim R = 1) : Function.Surjective (Module.Dual.eval R M) := by
  intro d
  have hp : (IsLocalRing.maximalIdeal R).height = 1 := by
    have hh := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hR] at hh
    exact_mod_cast hh
  obtain ⟨m, s, hs, hsm⟩ :=
    exists_smul_eq_dualEval_of_height_le_one (R := R) (M := M)
      (IsLocalRing.maximalIdeal R) (by simp [hp]) d
  have hu : IsUnit s := IsLocalRing.notMem_maximalIdeal.mp hs
  refine ⟨(↑hu.unit⁻¹ : R) • m, ?_⟩
  rw [map_smul, ← hsm, smul_smul, hu.val_inv_mul, one_smul]

/-! ### Membership in the image of the sections at the generic point -/

private theorem mem_range_iff_height_one_of_isReflexive
    {R M V : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsReflexive R M]
    [AddCommGroup V] [Module R V]
    (i : M →ₗ[R] V) [IsLocalizedModule (nonZeroDivisors R) i] (z : V) :
    z ∈ LinearMap.range i ↔
      ∀ (p : Ideal R) (_ : p.IsPrime), p.height = 1 →
        ∃ (m : M) (s : R), s ∉ p ∧ s • z = i m := by
  constructor
  · rintro ⟨m, rfl⟩ p hp _
    exact ⟨m, 1, fun h1 => hp.ne_top' (Ideal.eq_top_of_isUnit_mem p h1 isUnit_one), by simp⟩
  · intro hz
    let S := nonZeroDivisors R
    let j := LocalizedModule.mkLinearMap S M
    let D := Module.Dual R (Module.Dual R M)
    let jD := LocalizedModule.mkLinearMap S D
    let e := IsLocalizedModule.iso S i
    have hloc : ∀ (p : Ideal R) (_ : p.IsPrime), p.height = 1 →
        ∃ (m : M) (s : R), s ∉ p ∧ s • e.symm z = j m := by
      intro p hp hheight
      obtain ⟨m, s, hs, hsm⟩ := hz p hp hheight
      refine ⟨m, s, hs, ?_⟩
      have h := congrArg e.symm hsm
      simpa only [e, map_smul, IsLocalizedModule.iso_symm_apply, j,
        LocalizedModule.mkLinearMap_apply] using h
    obtain ⟨d, hd⟩ := ((reflexiveHull_eq_iInf_localization_mod_torsion
      (R := R) (M := M) (e.symm z)).1).mpr hloc
    obtain ⟨m, hm⟩ := Module.IsReflexive.bijective_dual_eval' (R := R) (M := M) |>.2 d
    have heval : Function.Injective (Module.Dual.eval R M) :=
      Module.IsReflexive.bijective_dual_eval' (R := R) (M := M) |>.1
    have hj : j m = e.symm z :=
      IsLocalizedModule.map_injective S j jD (Module.Dual.eval R M) heval
        (by rwa [IsLocalizedModule.map_apply, hm])
    refine ⟨m, ?_⟩
    apply e.symm.injective
    simpa only [e, IsLocalizedModule.iso_symm_apply, j,
      LocalizedModule.mkLinearMap_apply] using hj

/-! ### The stalk of the reflexive hull is the double dual of the stalk -/

/-- The stalk of `ℱ^∨∨` at `x`, read as the double `𝒪_{X,x}`-dual of the stalk of `ℱ`. -/
private noncomputable def hullStalkEquiv {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] [(dualSheaf F).IsFinitePresentation] (x : X) :
    (reflexiveHull F).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      Module.Dual (X.presheaf.stalk x)
        (Module.Dual (X.presheaf.stalk x) (F.presheaf.stalk x)) :=
  (dualStalkEquiv (dualSheaf F) x).trans
    (LinearEquiv.arrowCongr (dualStalkEquiv F x) (LinearEquiv.refl _ _))

private theorem hullStalkEquiv_toDoubleDual {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] [(dualSheaf F).IsFinitePresentation] (x : X)
    (m : F.presheaf.stalk x) :
    hullStalkEquiv F x (stalkMapOfHom (toDoubleDual F) x m) =
      Module.Dual.eval (X.presheaf.stalk x) (F.presheaf.stalk x) m := by
  ext l
  show dualStalkEquiv (dualSheaf F) x (stalkMapOfHom (toDoubleDual F) x m)
    ((dualStalkEquiv F x).symm l) = l m
  rw [← dualStalkEquiv_eq_dualStalkEquiv_toDoubleDual]
  exact congrArg (fun f : Module.Dual (X.presheaf.stalk x) (F.presheaf.stalk x) => f m)
    ((dualStalkEquiv F x).apply_symm_apply l)

/-! ### Injectivity and surjectivity of the canonical map on stalks -/

private theorem dual_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] :
    (dualSheaf F).IsFinitePresentation :=
  have : _root_.SheafOfModules.IsCoherent (dualSheaf F) := isCoherent_dualSheaf F
  _root_.isFinitePresentation_of_isCoherent _

private theorem generic_toDoubleDual_injective (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] :
    Function.Injective (stalkMapOfHom (toDoubleDual F) (genericPoint X)) := by
  have : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  have := dual_isFinitePresentation F
  intro m n h
  apply Module.eval_apply_injective (X.presheaf.stalk (genericPoint X))
    (V := F.presheaf.stalk (genericPoint X))
  simpa only [hullStalkEquiv_toDoubleDual] using
    congrArg (hullStalkEquiv F (genericPoint X)) h

private theorem toDoubleDual_stalk_surjective_of_dim_one (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) = 1) :
    Function.Surjective (stalkMapOfHom (toDoubleDual F) x) := by
  have : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  have : F.IsFiniteType := _root_.IsCoherent.toIsFiniteType F
  have := dual_isFinitePresentation F
  have : Module.Finite ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    Stacks.StalkFiniteType.finite_stalk F x
  have := IsNormal.stalk_normal (X := X) x
  intro z
  obtain ⟨m, hm⟩ := dualEval_surjective_of_local_dim_one
    (M := F.presheaf.stalk x) hx (hullStalkEquiv F x z)
  exact ⟨m, (hullStalkEquiv F x).injective
    ((hullStalkEquiv_toDoubleDual F x m).trans hm)⟩

/-! ### Gluing a section-level extension -/

private theorem section_eq_zero_of_generic_germ_eq_zero (X : Scheme.{u}) [IsIntegral X]
    {F : X.Modules} [F.IsQuasicoherent] (hF : IsTorsionFree F) (U : X.Opens) [Nonempty U]
    (s : Γ(F, U))
    (hs : F.presheaf.germ U (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using (inferInstance : Nonempty U))) s = 0) :
    s = 0 :=
  hF U s ((torsion_section_tfae X F U s).out 3 2 |>.mp hs)

private theorem generic_germ_injective {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F) {U : X.Opens}
    (hη : genericPoint X ∈ U) :
    Function.Injective (F.presheaf.germ U (genericPoint X) hη) := by
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  intro a b hab
  apply sub_eq_zero.mp
  apply section_eq_zero_of_generic_germ_eq_zero X (isTorsionFree_of_isReflexive F hF) U
  simpa only [map_sub, sub_eq_zero] using hab

private theorem stalkSpecializes_sections_smul {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (x y : U) (h : x.1 ⤳ y.1) (r : Γ(X, U)) (m : F.presheaf.stalk y) :
    letI := affineStalkModule F U x x.2
    letI := affineStalkModule F U y y.2
    F.presheaf.stalkSpecializes h (r • m) = r • F.presheaf.stalkSpecializes h m := by
  show F.presheaf.stalkSpecializes h (X.presheaf.germ U y y.2 r • m) =
    X.presheaf.germ U x x.2 r • F.presheaf.stalkSpecializes h m
  rw [Stacks.ModuleStalkSpecialization.stalkSpecializes_smul F h,
    Stacks.ModuleStalkSpecialization.ringGerm_stalkSpecializes_apply y.2 h]

private theorem affineGenericGerm_isLocalizedModule {X : Scheme.{u}} [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (hη : genericPoint X ∈ U) :
    letI := affineStalkModule F U (genericPoint X) hη
    IsLocalizedModule (nonZeroDivisors Γ(X, U)) (affineGerm F U (genericPoint X) hη) := by
  have : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  have h := affineGerm_isLocalized F U hU (genericPoint X) hη
  have hp : (hU.primeIdealOf ⟨genericPoint X, hη⟩).asIdeal.primeCompl =
      nonZeroDivisors Γ(X, U) := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    exact Ideal.primeCompl_bot
  rwa [hp] at h

private theorem ringKrullDim_stalk_eq_height {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) :
    ringKrullDim ↑(X.presheaf.stalk x.1) = (hU.primeIdealOf x).asIdeal.height :=
  let := X.presheaf.algebra_section_stalk x
  let := hU.isLocalization_stalk x
  IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf x).asIdeal _

private theorem affine_generic_mem_range {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F) {U : X.Opens}
    (hU : IsAffineOpen U) (hη : genericPoint X ∈ U) (z : F.presheaf.stalk (genericPoint X))
    (hz : ∀ x : U, ringKrullDim (X.presheaf.stalk x) = 1 →
      z ∈ Set.range (F.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes (Set.mem_univ x.1)))) :
    z ∈ Set.range (F.presheaf.germ U (genericPoint X) hη) := by
  have : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have : F.IsFiniteType := _root_.IsCoherent.toIsFiniteType F
  have := Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F hU
  have := (isReflexive_iff_sections_isReflexive X F).mp hF U hU
  let := affineStalkModule F U (genericPoint X) hη
  have := affineGenericGerm_isLocalizedModule F hU hη
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := (isNormal_iff_forall_affineOpen_normal X).mp inferInstance ⟨U, hU⟩ inferInstance
  show z ∈ LinearMap.range (affineGerm F U (genericPoint X) hη)
  apply (mem_range_iff_height_one_of_isReflexive _ z).mpr
  intro p hp hheight
  let q : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  let x : U := ⟨hU.fromSpec q, (hU.isoSpec.inv q).2⟩
  have hx : hU.primeIdealOf x = q :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf x)
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_height hU x, hx]
    exact_mod_cast hheight
  obtain ⟨w, hw⟩ := hz x hdim
  let := affineStalkModule F U x x.2
  have := affineGerm_isLocalized F U hU x x.2
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (hU.primeIdealOf x).asIdeal.primeCompl
    (affineGerm F U x x.2) w
  refine ⟨m, s, by simpa [hx, q] using s.property, ?_⟩
  let h : genericPoint X ⤳ x.1 := (genericPoint_spec X).specializes trivial
  calc
    (s : Γ(X, U)) • z = (s : Γ(X, U)) • F.presheaf.stalkSpecializes h w := by rw [hw]
    _ = F.presheaf.stalkSpecializes h ((s : Γ(X, U)) • w) :=
      (stalkSpecializes_sections_smul F ⟨genericPoint X, hη⟩ x h s w).symm
    _ = F.presheaf.stalkSpecializes h (affineGerm F U x x.2 m) := congrArg _ hs
    _ = affineGerm F U (genericPoint X) hη m :=
      ConcreteCategory.congr_hom (F.presheaf.germ_stalkSpecializes x.2 h) m

private theorem generic_mem_range {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (U : X.Opens) (hη : genericPoint X ∈ U) (z : F.presheaf.stalk (genericPoint X))
    (hz : ∀ x : U, ringKrullDim (X.presheaf.stalk x) = 1 →
      z ∈ Set.range (F.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes (Set.mem_univ x.1)))) :
    z ∈ Set.range (F.presheaf.germ U (genericPoint X) hη) := by
  classical
  choose V hV hxV hVU using fun x : U => exists_isAffineOpen_mem_and_subset x.2
  have hηV (x : U) : genericPoint X ∈ V x :=
    ((genericPoint_spec X).specializes (Set.mem_univ x.1)).mem_open (V x).isOpen (hxV x)
  have hex (x : U) : ∃ s : Γ(F, V x), F.presheaf.germ (V x) (genericPoint X) (hηV x) s = z :=
    affine_generic_mem_range F hF (hV x) (hηV x) z (fun y hy => hz ⟨y, hVU x y.2⟩ hy)
  choose s hs using hex
  have hc : F.presheaf.IsCompatible V s := by
    intro x y
    apply generic_germ_injective F hF (show genericPoint X ∈ V x ⊓ V y from ⟨hηV x, hηV y⟩)
    rw [F.presheaf.germ_res_apply, F.presheaf.germ_res_apply, hs, hs]
  have hcov : U ≤ iSup V := fun x hx => (Opens.leSupr V ⟨x, hx⟩).le (hxV ⟨x, hx⟩)
  obtain ⟨t, ht, -⟩ :=
    (show TopCat.Sheaf Ab X.toTopCat from ⟨F.presheaf, F.isSheaf⟩).existsUnique_gluing'
      V U (fun x => homOfLE (hVU x)) hcov s hc
  refine ⟨t, ?_⟩
  let x : U := ⟨genericPoint X, hη⟩
  have h := congrArg (F.presheaf.germ (V x) (genericPoint X) (hηV x)) (ht x)
  exact (F.presheaf.germ_res_apply (homOfLE (hVU x)) _ (hηV x) t).symm.trans (h.trans (hs x))

/-- On an integral scheme a module has at most one section over an open set that misses the
generic point. -/
theorem subsingleton_sections_of_not_generic_mem {X : Scheme.{u}} [IsIntegral X]
    (F : X.Modules) (U : X.Opens) (hη : genericPoint X ∉ U) : Subsingleton Γ(F, U) := by
  have hU : U = ⊥ := bot_unique fun x hx => False.elim (hη
    (((genericPoint_spec X).specializes (Set.mem_univ x)).mem_open U.isOpen hx))
  let hterm : Limits.IsTerminal (F.presheaf.obj (op U)) :=
    TopCat.Sheaf.isTerminalOfEqEmpty ⟨F.presheaf, F.isSheaf⟩ hU
  have := Limits.Concrete.uniqueOfTerminalOfPreserves _ hterm
  infer_instance

private theorem exists_hom_of_codimension_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (T : G.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
      F.presheaf.stalk (genericPoint X))
    (hT : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      Set.MapsTo T (Set.range (G.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes (Set.mem_univ x))))
        (Set.range (F.presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes (Set.mem_univ x))))) :
    ∃ e : G ⟶ F, ∀ m,
      ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map e.mapPresheaf) m = T m := by
  classical
  let η := genericPoint X
  let P (U : X.Opens) (m : Γ(G, U)) (s : Γ(F, U)) :=
    ∀ hη : η ∈ U, F.presheaf.germ U η hη s = T (G.presheaf.germ U η hη m)
  have hex (U : X.Opens) (m : Γ(G, U)) : ∃! s : Γ(F, U), P U m s := by
    by_cases hη : η ∈ U
    · obtain ⟨s, hs⟩ := generic_mem_range F hF U hη (T (G.presheaf.germ U η hη m))
        (fun x hx => hT x hx ⟨G.presheaf.germ U x x.2 m,
          ConcreteCategory.congr_hom (G.presheaf.germ_stalkSpecializes x.2
            ((genericPoint_spec X).specializes (Set.mem_univ x.1))) m⟩)
      exact ⟨s, fun _ => hs, fun t ht => generic_germ_injective F hF hη ((ht hη).trans hs.symm)⟩
    · have := subsingleton_sections_of_not_generic_mem F U hη
      exact ⟨0, fun h => (hη h).elim, fun _ _ => Subsingleton.elim _ _⟩
  let f (U : X.Opens) (m : Γ(G, U)) := (hex U m).choose
  have hf (U : X.Opens) (m : Γ(G, U)) : P U m (f U m) := (hex U m).choose_spec.1
  have hu (U : X.Opens) (m : Γ(G, U)) (s : Γ(F, U)) (hs : P U m s) : s = f U m :=
    (hex U m).choose_spec.2 s hs
  let e : G ⟶ F := ⟨{
    app := fun U => ModuleCat.ofHom {
      toFun := f U.unop
      map_add' := fun a b => by
        refine (hu _ _ _ fun hη => ?_).symm
        change Γ(G, U.unop) at a
        change Γ(G, U.unop) at b
        calc F.presheaf.germ U.unop η hη (f U.unop a + f U.unop b)
            = F.presheaf.germ U.unop η hη (f U.unop a) +
                F.presheaf.germ U.unop η hη (f U.unop b) := map_add _ _ _
          _ = T (G.presheaf.germ U.unop η hη a) + T (G.presheaf.germ U.unop η hη b) := by
            rw [hf U.unop a hη, hf U.unop b hη]
          _ = T (G.presheaf.germ U.unop η hη a + G.presheaf.germ U.unop η hη b) :=
            (T.map_add _ _).symm
          _ = T (G.presheaf.germ U.unop η hη (a + b)) :=
            congrArg T (map_add _ _ _).symm
      map_smul' := fun r m => by
        change Γ(X, U.unop) at r
        change Γ(G, U.unop) at m
        refine (hu _ _ _ fun hη => ?_).symm
        show F.presheaf.germ U.unop η hη (r • f U.unop m) =
          T (G.presheaf.germ U.unop η hη (r • m))
        refine Eq.trans (F.val.germ_smul (R := X.presheaf) η U.unop hη r _) ?_
        refine Eq.trans (congrArg (fun z : ↑(F.presheaf.stalk η) =>
          X.presheaf.germ U.unop η hη r • z) (hf U.unop m hη)) ?_
        exact (T.map_smul _ _).symm.trans
          (congrArg T (G.val.germ_smul (R := X.presheaf) η U.unop hη r m).symm) }
    naturality := fun {U V} i => by
      ext m
      change Γ(G, U.unop) at m
      refine (hu _ _ _ fun hη => ?_).symm
      show F.presheaf.germ V.unop η hη (F.presheaf.map i (f U.unop m)) =
          T (G.presheaf.germ V.unop η hη (G.presheaf.map i m))
      exact (F.presheaf.germ_res_apply i.unop η hη (f U.unop m)).trans
        ((hf U.unop m (i.unop.le hη)).trans
          (congrArg T (G.presheaf.germ_res_apply i.unop η hη m)).symm) }⟩
  refine ⟨e, fun m => ?_⟩
  obtain ⟨U, hη, m, rfl⟩ := G.presheaf.exists_germ_eq m
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact hf U m hη

private theorem mapsTo_stalkSpecializes_range {X : Scheme.{u}} {F G : X.Modules} (e : G ⟶ F)
    {x y : X} (h : x ⤳ y) :
    Set.MapsTo ((TopCat.Presheaf.stalkFunctor Ab x).map e.mapPresheaf)
      (Set.range (G.presheaf.stalkSpecializes h))
      (Set.range (F.presheaf.stalkSpecializes h)) := by
  rintro z ⟨m, rfl⟩
  refine ⟨((TopCat.Presheaf.stalkFunctor Ab y).map e.mapPresheaf) m, ?_⟩
  exact (ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map e.mapPresheaf h) m).symm

private theorem mapsTo_stalkSpecializes_range_of_lift {X : Scheme.{u}} {F G H : X.Modules}
    (j : F ⟶ H) (e : G ⟶ H) {x y : X} (h : x ⤳ y) (T : G.presheaf.stalk x → F.presheaf.stalk x)
    (he : ∀ m, ((TopCat.Presheaf.stalkFunctor Ab x).map e.mapPresheaf) m =
      ((TopCat.Presheaf.stalkFunctor Ab x).map j.mapPresheaf) (T m))
    (hjx : Function.Injective ((TopCat.Presheaf.stalkFunctor Ab x).map j.mapPresheaf))
    (hjy : Function.Surjective ((TopCat.Presheaf.stalkFunctor Ab y).map j.mapPresheaf)) :
    Set.MapsTo T (Set.range (G.presheaf.stalkSpecializes h))
      (Set.range (F.presheaf.stalkSpecializes h)) := by
  rintro z ⟨m, rfl⟩
  obtain ⟨n, hn⟩ := hjy (((TopCat.Presheaf.stalkFunctor Ab y).map e.mapPresheaf) m)
  refine ⟨n, ?_⟩
  apply hjx
  have hj : ((TopCat.Presheaf.stalkFunctor Ab x).map j.mapPresheaf)
      (F.presheaf.stalkSpecializes h n) =
      H.presheaf.stalkSpecializes h
        (((TopCat.Presheaf.stalkFunctor Ab y).map j.mapPresheaf) n) :=
    ConcreteCategory.congr_hom
      (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map j.mapPresheaf h) n
  have hee : ((TopCat.Presheaf.stalkFunctor Ab x).map e.mapPresheaf)
      (G.presheaf.stalkSpecializes h m) =
      H.presheaf.stalkSpecializes h
        (((TopCat.Presheaf.stalkFunctor Ab y).map e.mapPresheaf) m) :=
    ConcreteCategory.congr_hom
      (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map e.mapPresheaf h) m
  rw [hj, hn, ← hee]
  exact he _

/-! ### The extension criterion -/

/-- The generic stalk of an `𝒪_X`-module on an integral scheme, as a module over the function
field of `X`. -/
public noncomputable instance genericStalkModule (X : Scheme.{u}) [IsIntegral X]
    (F : X.Modules) : Module X.functionField (F.presheaf.stalk (genericPoint X)) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val (genericPoint X)

/-- On an integral locally Noetherian normal scheme, a linear map of generic stalks extends to a
map into the reflexive hull of its target if and only if, at every point whose local ring has
dimension one, it carries the image of the source stalk into the image of the target stalk. -/
@[stacks 0AY7]
theorem exists_lift_toReflexiveHull_iff_codimension_one (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (T : (G.presheaf.stalk (genericPoint X)) →ₗ[X.functionField]
      (F.presheaf.stalk (genericPoint X))) :
    (∃ e : G ⟶ reflexiveHull F,
      ∀ m : G.presheaf.stalk (genericPoint X),
        ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
          (Scheme.Modules.Hom.mapPresheaf (X := X) e)) m =
          ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
            (Scheme.Modules.Hom.mapPresheaf (X := X)
              (toReflexiveHull F).1)) (T m)) ↔
      ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
        let h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
        Set.MapsTo T (Set.range (G.presheaf.stalkSpecializes h))
          (Set.range (F.presheaf.stalkSpecializes h)) := by
  constructor
  · rintro ⟨e, he⟩ x hx
    exact mapsTo_stalkSpecializes_range_of_lift (toReflexiveHull F).1 e _ T he
      (generic_toDoubleDual_injective X F)
      (toDoubleDual_stalk_surjective_of_dim_one X F x hx)
  · intro hT
    have : _root_.SheafOfModules.IsCoherent (reflexiveHull F) := isCoherent_doubleDual F
    have : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
    have := dual_isFinitePresentation F
    let S : G.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
        (reflexiveHull F).presheaf.stalk (genericPoint X) :=
      (hullStalkEquiv F (genericPoint X)).symm.toLinearMap.comp
        ((Module.Dual.eval (X.presheaf.stalk (genericPoint X))
          (F.presheaf.stalk (genericPoint X))).comp T)
    have hS (m : G.presheaf.stalk (genericPoint X)) :
        S m = stalkMapOfHom (toDoubleDual F) (genericPoint X) (T m) :=
      (hullStalkEquiv F (genericPoint X)).injective
        (((hullStalkEquiv F (genericPoint X)).apply_symm_apply _).trans
          (hullStalkEquiv_toDoubleDual F (genericPoint X) (T m)).symm)
    obtain ⟨e, he⟩ := exists_hom_of_codimension_one (reflexiveHull F) G
      (isReflexive_reflexiveHull X F) S
      (fun x hx m hm => by
        rw [hS]
        exact mapsTo_stalkSpecializes_range (toReflexiveHull F).1 _ (hT x hx hm))
    exact ⟨e, fun m => (he m).trans (hS m)⟩

end AlgebraicGeometry

end
