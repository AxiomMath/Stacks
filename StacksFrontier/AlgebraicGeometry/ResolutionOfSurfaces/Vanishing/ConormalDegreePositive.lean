module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.QuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FibrePrincipalDictionary
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.StalkIdeal
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.SchemeModulesSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.BaseToStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentCurveDichotomy
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentDiscreteValuation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentStalkKernel
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ConormalDegree
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.GenericPointSection
public import StacksFrontier.RingTheory.Ideal.PrincipalRadical.DivisorOfGenerator

/-!
# The conormal sheaf of a divisor in the special fibre has positive degree on a component

In Situation [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local domain `A` and a
modification `f : X ⟶ S = Spec(A)` with the irreducible components `C_1, …, C_r` of the special
fibre enumerated — let `X` be normal and let `Z ⊆ X` be a nonempty effective Cartier divisor with
`Z ⊆ X_s` set theoretically. [Stacks, Tag 0AXA] says that the conormal sheaf of `Z` is not
trivial, and more precisely that some `C_i ⊆ Z` has `deg(𝒞_{Z/X}|_{C_i}) > 0`. This file proves
both clauses under exactly those hypotheses, constructing the section of the source's proof.

## Main results

The elided prefix is `AlgebraicGeometry.VanishingSituation`.

* `exists_subset_invertibleCurveDegree_conormalOnComponent_pos`: **Tag 0AXA**, the precise
  clause.
* `not_isTrivial_conormalSheaf_of_nonempty`: **Tag 0AXA**, the first clause.
* `topologicalKrullDim_componentScheme_le_one_of_isNormal`: each `C_i`, with its reduced induced
  structure, has dimension at most one (`topologicalKrullDim_component_le_one`, via
  [Stacks, Tags 0BAE, 053V]), so the degree of an invertible sheaf on it is defined.
* `topologicalKrullDim_component_eq_one_of_stalk`,
  `topologicalKrullDim_component_eq_one_of_isEffectiveCartierDivisor`: the standing observation
  following Situation 0AX8 that every `C_i` is a curve, proved as soon as some point over the
  closed point has a local ring of dimension other than two — in particular once the special
  fibre contains a nonempty effective Cartier divisor. The source obtains it by
  discarding the case of a zero-dimensional special fibre; here [Stacks, Tag 0BFP] is what rules
  out a zero-dimensional component.
* `exists_eq_componentGenericPoint_of_isGenericPoint`: the generic points of the components of `Z`
  are generic points of components of the special fibre.
* `invertibleCurveDegree_conormalOnComponent_pow`:
  `deg(𝒞_{nZ/X}|_{C_i}) = n · deg(𝒞_{Z/X}|_{C_i})`, the replacement of `Z` by `e_i Z`
  ([Stacks, Tags 02OP, 0B3P, 0AYX]).
* `Stacks.ModuleStalk.Γgerm_notMem_maximalSmul`, `Stacks.ModuleStalk.Γgerm_mem_maximalSmul`: the
  nonvanishing of a global section of a subsheaf of `𝒪_X` read off in the local ring.

## The proof

As in the source. Let `a ∈ 𝔪` be the function of [Stacks, Tag 0AX9] with its points `x_i` and
factorizations `a = g_i h_i`. The local rings at the generic points `ξ_j` are discrete valuation
rings ([Stacks, Tag 00PD]); with `e_j` the valuation of `a` and `d_j` that of a local equation of
`Z`, choose `i` with `d_i / e_i` maximal. Then `a^{d_i}` lies in `ℐ_{e_i Z}` at every generic point
of `e_i Z`, hence globally since `e_i Z` is `(S_1)` ([Stacks, Tags 0B3S, 0346, 0B3M]); its
restriction to `C_i` is nonzero because it generates `ℐ_{e_i Z}` at `ξ_i`, and it vanishes at
`x_i` by Krull's principal ideal theorem applied to `g_i`. Part (2) of [Stacks, Tag 0B40] gives
`deg(𝒞_{e_i Z/X}|_{C_i}) > 0`, which is `e_i · deg(𝒞_{Z/X}|_{C_i})`. The nonvanishing loci are
compared along `C_i ⟶ X` by [Stacks, Tag 0H78].

## References

* [Stacks Project, Tag 0AXA](https://stacks.math.columbia.edu/tag/0AXA)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AX9](https://stacks.math.columbia.edu/tag/0AX9)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0B3S](https://stacks.math.columbia.edu/tag/0B3S)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

/-! ### Nonvanishing of a global section of a subsheaf of `𝒪_X`, read in the local ring -/

namespace Stacks.ModuleStalk

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} {M : X.Modules} (ι : M ⟶ Stacks.Ample.unitModule X)

/-- The stalk at `x` of a morphism `M ⟶ 𝒪_X`, with values in the local ring `𝒪_{X,x}`. -/
noncomputable def stalkToLocalRing (x : X) :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x →+ X.presheaf.stalk x :=
  AddMonoidHom.mk' (fun m => Stacks.Ample.unitStalkFun X x (mapFun ι x m))
    (fun m m' => by
      change Stacks.Ample.unitStalkFun X x (mapFun ι x (m + m')) = _
      rw [mapFun_add]
      exact Stacks.Ample.unitStalkFun_add X x _ _)

/-- On the germ of a section `t` of `M` over `U`, `stalkToLocalRing ι x` is the germ of
`ι.app U t`. -/
theorem stalkToLocalRing_germ (x : X) (U : X.Opens) (hx : x ∈ U) (t : Γ(M, U)) :
    stalkToLocalRing ι x ((M.presheaf.germ U x hx).hom t) =
      (X.presheaf.germ U x hx).hom (ι.app U t : Γ(X, U)) := by
  change Stacks.Ample.unitStalkFun X x (mapFun ι x _) = _
  rw [mapFun_germ]
  exact Stacks.Ample.unitStalkFun_germ X x U hx _

/-- `stalkToLocalRing ι x` is `𝒪_{X,x}`-linear: it sends `r • m` to `r` times the image of `m`. -/
theorem stalkToLocalRing_smul (x : X) (r : X.presheaf.stalk x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    stalkToLocalRing ι x (r • m) = r * stalkToLocalRing ι x m := by
  change Stacks.Ample.unitStalkFun X x (mapFun ι x _) =
    r * Stacks.Ample.unitStalkFun X x (mapFun ι x m)
  rw [mapFun_smul]
  exact Stacks.Ample.unitStalkFun_smul X x r _

/-- The image of the stalk of a morphism `M ⟶ 𝒪_X`, an ideal of the local ring. -/
noncomputable def rangeIdeal (x : X) : Ideal (X.presheaf.stalk x) where
  carrier := Set.range (stalkToLocalRing ι x)
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨m', rfl⟩
    exact ⟨m + m', map_add _ m m'⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨m, rfl⟩
    exact ⟨r • m, stalkToLocalRing_smul ι x r m⟩

/-- The stalk of a morphism `M ⟶ 𝒪_X` which is injective on sections is injective. -/
theorem stalkToLocalRing_injective (hι : ∀ W : X.Opens, Function.Injective (ι.app W)) (x : X) :
    Function.Injective (stalkToLocalRing ι x) := by
  refine (injective_iff_map_eq_zero _).mpr fun m hm => ?_
  obtain ⟨U, hxU, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  rw [stalkToLocalRing_germ] at hm
  have h0 : (X.presheaf.germ U x hxU).hom (ι.app U b : Γ(X, U)) =
      (X.presheaf.germ U x hxU).hom 0 := by rw [hm, map_zero]
  obtain ⟨W, hxW, iU, iV, hW⟩ := X.presheaf.germ_eq x hxU hxU _ _ h0
  have hnat := ConcreteCategory.congr_hom (ι.mapPresheaf.naturality iU.op) b
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hnat
  have hb0 : M.presheaf.map iU.op b = 0 := by
    apply hι W
    rw [hnat, map_zero]
    change X.presheaf.map iU.op (ι.app U b : Γ(X, U)) = 0
    rw [hW, map_zero]
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf iU x hxW b, hb0, map_zero]

/-- **A global section of a subsheaf of `𝒪_X` does not vanish at `x` when its image avoids
`𝔪_x J`**, for an ideal `J ⊆ 𝒪_{X,x}` containing the germs of all local sections. -/
theorem Γgerm_notMem_maximalSmul (x : X) (J : Ideal (X.presheaf.stalk x))
    (hJ : ∀ (U : X.Opens) (hx : x ∈ U) (t : Γ(M, U)),
      (X.presheaf.germ U x hx).hom (ι.app U t : Γ(X, U)) ∈ J)
    (b : Γ(M, ⊤))
    (hb : (X.presheaf.germ ⊤ x (Opens.mem_top x)).hom (ι.app ⊤ b : Γ(X, ⊤)) ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) * J) :
    (M.presheaf.germ ⊤ x (Opens.mem_top x)).hom b ∉ maximalSmul M x := by
  intro hmem
  apply hb
  rw [← stalkToLocalRing_germ]
  refine Submodule.smul_induction_on hmem (fun r hr n _ => ?_) (fun a b ha hb => ?_)
  · rw [stalkToLocalRing_smul]
    obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf n
    rw [stalkToLocalRing_germ]
    exact Ideal.mul_mem_mul hr (hJ U hxU t)
  · rw [map_add]
    exact add_mem ha hb

/-- **A global section of a subsheaf of `𝒪_X` vanishes at `x` when its image lies in `𝔪_x J`**,
for an ideal `J ⊆ 𝒪_{X,x}` all of whose elements are germs of local sections, provided `M ⟶ 𝒪_X`
is injective on sections. -/
theorem Γgerm_mem_maximalSmul (hι : ∀ W : X.Opens, Function.Injective (ι.app W)) (x : X)
    (J : Ideal (X.presheaf.stalk x)) (hJ : ∀ y ∈ J, ∃ n, stalkToLocalRing ι x n = y)
    (b : Γ(M, ⊤))
    (hb : (X.presheaf.germ ⊤ x (Opens.mem_top x)).hom (ι.app ⊤ b : Γ(X, ⊤)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) * J) :
    (M.presheaf.germ ⊤ x (Opens.mem_top x)).hom b ∈ maximalSmul M x := by
  rw [← stalkToLocalRing_germ] at hb
  obtain ⟨n, hn, hn'⟩ : ∃ n ∈ maximalSmul M x, stalkToLocalRing ι x n =
      stalkToLocalRing ι x ((M.presheaf.germ ⊤ x (Opens.mem_top x)).hom b) := by
    refine Submodule.mul_induction_on hb (fun r hr y hy => ?_) (fun y y' hy hy' => ?_)
    · obtain ⟨n, rfl⟩ := hJ y hy
      exact ⟨r • n, smul_mem_maximalSmul_of_mem_maximalIdeal hr n,
        stalkToLocalRing_smul ι x r n⟩
    · obtain ⟨n, hn, rfl⟩ := hy
      obtain ⟨n', hn', rfl⟩ := hy'
      exact ⟨n + n', add_mem hn hn', map_add _ n n'⟩
  rwa [← stalkToLocalRing_injective ι hι x hn']

end Stacks.ModuleStalk

namespace Stacks.Divisors

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The inclusion of the ideal sheaf into the structure sheaf is injective on sections. -/
theorem idealInclusion_app_injective (W : X.Opens) :
    Function.Injective ((idealInclusion D).val.app (op W)).hom := by
  intro b b' h
  rw [← kernelSection_kernelIdealSheafIso_hom, ← kernelSection_kernelIdealSheafIso_hom] at h
  have h' := kernelSection_injective D h
  have key : ∀ c, ((kernelIdealSheafIso D).inv.val.app (op W)).hom
      (((kernelIdealSheafIso D).hom.val.app (op W)).hom c) = c := fun c => by
    change (((kernelIdealSheafIso D).hom ≫ (kernelIdealSheafIso D).inv).val.app (op W)).hom c = c
    rw [(kernelIdealSheafIso D).hom_inv_id]
    rfl
  rw [← key b, ← key b', h']

/-- The germ of a function on `U` vanishing on `D` lies in the ideal `ℐ_{D,x}`. -/
private theorem germ_mem_stalkIdeal_of_mem_ker (U : X.Opens) (x : X) (hs : x ∈ D.support)
    (hx : x ∈ U) (τ : Γ(X, U)) (hτ : τ ∈ RingHom.ker (D.subschemeι.app U).hom) :
    (X.presheaf.germ U x hx).hom τ ∈ Stacks.AlgebraicGeometry.stalkIdeal D x hs := by
  change _ ∈ RingHom.ker (D.subschemeι.stalkMap (⟨x, hs⟩ : D.subscheme)).hom
  exact RingHom.mem_ker.mpr
    ((Scheme.Hom.germ_stalkMap_apply D.subschemeι U ⟨x, hs⟩ hx τ).trans
      (by rw [RingHom.mem_ker.mp hτ, map_zero]))

/-- The germs of the local sections of `ℐ_D` lie in the ideal `ℐ_{D,x}` cut out in the local
ring. -/
theorem germ_idealInclusion_mem_stalkIdeal (x : X) (hs : x ∈ D.support) (U : X.Opens)
    (hx : x ∈ U) (t : (negativeTwist D).val.obj (op U)) :
    (X.presheaf.germ U x hx).hom (((idealInclusion D).val.app (op U)).hom t : Γ(X, U)) ∈
      Stacks.AlgebraicGeometry.stalkIdeal D x hs := by
  have hker := kernelSection_mem D ((kernelIdealSheafIso D).hom.val.app (op U) t)
  rw [kernelSection_kernelIdealSheafIso_hom] at hker
  exact germ_mem_stalkIdeal_of_mem_ker D U x hs hx _ hker

/-- Every element of `ℐ_{D,x}` is the image of an element of the stalk of `ℐ_D`. -/
theorem exists_stalkToLocalRing_idealInclusion_eq (x : X) (hs : x ∈ D.support)
    (y : X.presheaf.stalk x) (hy : y ∈ Stacks.AlgebraicGeometry.stalkIdeal D x hs) :
    ∃ n, Stacks.ModuleStalk.stalkToLocalRing
      (M := (negativeTwist D : _root_.AlgebraicGeometry.Scheme.Modules X))
      (idealInclusion D) x n = y := by
  let S := Stacks.ModuleStalk.rangeIdeal
      (M := (negativeTwist D : _root_.AlgebraicGeometry.Scheme.Modules X)) (idealInclusion D) x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  rw [Stacks.AlgebraicGeometry.stalkIdeal_eq_map_germ D x hs hU hxU] at hy
  have hle : (D.ideal ⟨U, hU⟩).map (X.presheaf.germ U x hxU).hom ≤ S := by
    refine Ideal.map_le_iff_le_comap.mpr fun t ht => ?_
    obtain ⟨c, hc⟩ := (D.mem_range_idealSheaf_subschemeι_app_iff ⟨U, hU⟩ t).mpr ht
    refine ⟨((_root_.AlgebraicGeometry.Scheme.Modules.presheaf (X := X) (negativeTwist D)).germ
      U x hxU).hom c, ?_⟩
    refine (Stacks.ModuleStalk.stalkToLocalRing_germ _ x U hxU c).trans ?_
    exact congrArg (X.presheaf.germ U x hxU).hom hc
  exact hle hy

/-- At every point, `ℐ_{D,x}` is generated by a nonzero element, which is `1` off the support. -/
private theorem exists_stalkIdeal_eq_span_or_eq_one [hD : IsEffectiveCartierDivisor D] (x : X) :
    ∃ b : X.presheaf.stalk x, b ≠ 0 ∧
      (∀ hx : x ∈ D.support, Stacks.AlgebraicGeometry.stalkIdeal D x hx = Ideal.span {b}) ∧
      (x ∉ D.support → b = 1) := by
  by_cases hx : x ∈ D.support
  · obtain ⟨b, hb, hreg⟩ := exists_isRegular_stalkIdeal_eq_span D hD x hx
    exact ⟨b, hreg.ne_zero, fun _ => hb, fun h => absurd hx h⟩
  · exact ⟨1, one_ne_zero, fun h => absurd h hx, fun _ => rfl⟩

end Stacks.Divisors

namespace Stacks.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The ideal cut out in a local ring by `n D` is the `n`-th power of the one cut out by `D`. -/
theorem stalkIdeal_pow (x : X) (n : ℕ) (hxn : x ∈ (D ^ n).support) (hx : x ∈ D.support) :
    stalkIdeal (D ^ n) x hxn = stalkIdeal D x hx ^ n := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  rw [stalkIdeal_eq_map_germ (D ^ n) x hxn hU hxU, stalkIdeal_eq_map_germ D x hx hU hxU,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Ideal.map_pow]

/-- At a point of the support the ideal cut out in the local ring is proper. -/
theorem stalkIdeal_le_maximalIdeal (x : X) (hx : x ∈ D.support) :
    stalkIdeal D x hx ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  rw [stalkIdeal_eq_map_germ D x hx hU hxU]
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  have hz := (Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨U, hU⟩) hxU).mp
    (by simpa using hx)
  rw [Scheme.mem_zeroLocus_iff] at hz
  exact (IsLocalRing.mem_maximalIdeal _).mpr
    (fun hu => hz f hf ((Scheme.mem_basicOpen X f x hxU).mpr hu))

end Stacks.AlgebraicGeometry

namespace AlgebraicGeometry.VanishingSituation

variable (V : VanishingSituation.{u})

/-! ### The dimension of the components of the special fibre -/

/-- Each component of the special fibre, with its reduced induced structure, has dimension at
most one, for `X` normal. -/
theorem topologicalKrullDim_componentScheme_le_one_of_isNormal [IsNormal V.X]
    (i : Fin V.numberOfComponents) : topologicalKrullDim (componentScheme V i) ≤ 1 :=
  ((componentSchemeHomeo V i).isHomeomorph.topologicalKrullDim_eq).trans_le
    (topologicalKrullDim_component_le_one V i)

/-- The image of a point of a closed subscheme lies in the support. -/
private theorem subschemeι_mem_supportSet {X : Scheme.{u}} (I : X.IdealSheafData)
    (ξ : I.subscheme) : I.subschemeι ξ ∈ I.supportSet := by
  have h : I.subschemeι ξ ∈ Set.range I.subschemeι := ⟨ξ, rfl⟩
  rwa [I.range_subschemeι] at h

/-- A nonempty closed subscheme has a generic point of an irreducible component. -/
theorem exists_isGenericPoint_subscheme {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hne : I.supportSet.Nonempty) :
    ∃ ξ : I.subscheme, ∃ Z : irreducibleComponents I.subscheme, IsGenericPoint ξ Z := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨z, -⟩ : x ∈ Set.range I.subschemeι := by rwa [I.range_subschemeι]
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({z} : Set I.subscheme) isIrreducible_singleton
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  exact ⟨ξ, ⟨Z, hZ⟩, hξ⟩

/-- **Every component of the special fibre is a curve** as soon as some point of a normal `X` over
the closed point has a local ring of dimension other than two. This is the standing observation
following Situation [Stacks, Tag 0AX8]: a zero-dimensional component would be an isolated point of
the special fibre, so `f` would be quasi-finite there and hence, the base being normal, an
isomorphism over a neighbourhood of the closed point ([Stacks, Tag 0BFP]); but then every local
ring of `X` over the closed point would be the local ring `A` of the base, of dimension two. -/
theorem topologicalKrullDim_component_eq_one_of_stalk [IsNormal V.X] (x0 : V.X)
    (hfx0 : V.f x0 = V.closedPoint) (hdim1 : ringKrullDim (V.X.presheaf.stalk x0) ≠ 2)
    (i : Fin V.numberOfComponents) : topologicalKrullDim (V.component i) = 1 := by
  rcases isIso_f_or_forall_topologicalKrullDim_component_eq_one V with hiso | h
  · refine absurd ?_ hdim1
    rw [ringKrullDim_stalk_eq_coheight, coheight_eq_two_of_isIso V hfx0]
    rfl
  · exact h i

/-- **Every component of the special fibre is a curve** once the special fibre contains a
nonempty effective Cartier divisor of a normal `X`: at the generic point of a component of the
divisor the local ring has dimension one ([Stacks, Tag 0BCN]). -/
theorem topologicalKrullDim_component_eq_one_of_isEffectiveCartierDivisor [IsNormal V.X]
    (I : V.X.IdealSheafData)
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I] (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (i : Fin V.numberOfComponents) : topologicalKrullDim (V.component i) = 1 := by
  obtain ⟨ξ, Z, hξ⟩ := exists_isGenericPoint_subscheme I hne
  have hdim1 := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor I hI ξ ⟨Z, hξ⟩
  have hx0 := subschemeι_mem_supportSet I ξ
  have hfx0 : V.f (I.subschemeι ξ) = V.closedPoint := by
    obtain ⟨q, hq⟩ := hZs hx0
    have h : V.f.fiberι V.closedPoint q ∈ Set.range (V.f.fiberι V.closedPoint) := ⟨q, rfl⟩
    rwa [Scheme.Hom.range_fiberι, hq] at h
  refine topologicalKrullDim_component_eq_one_of_stalk V (I.subschemeι ξ) hfx0 ?_ i
  rw [hdim1]
  decide

/-! ### The degree of the restricted conormal sheaf of a multiple -/

open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible) in
/-- **The restricted conormal sheaf of `n Z` has `n` times the degree** of that of `Z`: its ideal
sheaf is `ℐ_Z^{⊗ n}` (`Stacks.Divisors.negativeTwistInvertibleTensorPowerIso`), pullback commutes
with tensor powers, and the degree of a tensor power is multiplicative ([Stacks, Tag 0AYX]). -/
theorem invertibleCurveDegree_conormalOnComponent_pow [IsNormal V.X] (I : V.X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor I] (i : Fin V.numberOfComponents) (n : ℕ) :
    invertibleCurveDegree (V.base.residueField V.closedPoint) (componentToSpecResidueField V i)
        (topologicalKrullDim_componentScheme_le_one_of_isNormal V i)
        (conormalOnComponent V (I ^ n) i) =
      n * invertibleCurveDegree (V.base.residueField V.closedPoint)
        (componentToSpecResidueField V i)
        (topologicalKrullDim_componentScheme_le_one_of_isNormal V i)
        (conormalOnComponent V I i) := by
  have : SheafOfModules.IsInvertible V.X.toRingedSpace.presheaf
      (structureSheafRing V.X.toRingedSpace).property (Stacks.Divisors.negativeTwist' I) :=
    Stacks.Divisors.isInvertible_negativeTwist I
  have : SheafOfModules.IsInvertible (componentScheme V i).toRingedSpace.presheaf
      (structureSheafRing (componentScheme V i).toRingedSpace).property
      ((Scheme.Modules.pullback (componentι V i)).obj (Stacks.Divisors.negativeTwist' I)) :=
    isInvertible_conormalOnComponent V I i
  let e : conormalOnComponent V (I ^ n) i ≅
      tensorPower (componentScheme V i).toRingedSpace.presheaf
        (structureSheafRing (componentScheme V i).toRingedSpace).property
        (conormalOnComponent V I i) (n : ℤ) :=
    (Scheme.Modules.pullback (componentι V i)).mapIso
        (Stacks.Divisors.negativeTwistInvertibleTensorPowerIso I n).symm ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso (componentι V i)
        (Stacks.Divisors.negativeTwist' I) n
  have : SheafOfModules.IsInvertible (componentScheme V i).presheaf
      (componentScheme V i).ringCatSheaf.2
      (tensorPower (componentScheme V i).toRingedSpace.presheaf
        (structureSheafRing (componentScheme V i).toRingedSpace).property
        (conormalOnComponent V I i) (n : ℤ)) :=
    tensorPower_isInvertible _ _ _ _
  rw [invertibleCurveDegree_eq_of_iso (V.base.residueField V.closedPoint)
    (componentToSpecResidueField V i) _ e]
  exact invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one
    (V.base.residueField V.closedPoint) (componentToSpecResidueField V i)
    (topologicalKrullDim_componentScheme_le_one_of_isNormal V i) (conormalOnComponent V I i) n

/-- **The generic points of the components of a divisor in the special fibre are generic points
of components of the special fibre.** The point lies on some component `C_j`, so it is a
specialization of `ξ_j`; both local rings have dimension one (the first by [Stacks, Tag 0BCN], the
second because `C_j` is a curve), so the specialization is trivial. -/
theorem exists_eq_componentGenericPoint_of_isGenericPoint [IsNormal V.X]
    (I : V.X.IdealSheafData) [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (ζ : I.subscheme) (hζ : ∃ Z : irreducibleComponents I.subscheme, IsGenericPoint ζ Z) :
    ∃ j : Fin V.numberOfComponents, I.subschemeι ζ = componentGenericPoint V j := by
  have hx0 := subschemeι_mem_supportSet I ζ
  have hdim := topologicalKrullDim_component_eq_one_of_isEffectiveCartierDivisor V I ⟨_, hx0⟩ hZs
  obtain ⟨q, hq⟩ := hZs hx0
  obtain ⟨Z, hZ, hqZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({q} : Set V.specialFiber) isIrreducible_singleton
  obtain ⟨j, rfl⟩ := V.exists_component_eq Z hZ
  refine ⟨j, ?_⟩
  have hsp : componentGenericPoint V j ⤳ I.subschemeι ζ := by
    rw [← hq]
    exact ((componentFiberGenericPoint_spec V j).specializes (hqZ rfl)).map
      (V.f.fiberι V.closedPoint).continuous
  by_contra hne'
  have hlt : I.subschemeι ζ < componentGenericPoint V j := by
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp) fun hge => hne' ?_
    exact ((Scheme.le_iff_specializes.mp hge).antisymm hsp).eq
  have h1 := Order.coheight_add_one_le hlt
  rw [coheight_componentGenericPoint_eq_one V hdim j] at h1
  have h2 := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor I hI ζ hζ
  rw [ringKrullDim_stalk_eq_coheight] at h2
  have h3 : Order.coheight (I.subschemeι ζ) = 1 := by exact_mod_cast h2
  rw [h3] at h1
  exact absurd h1 (by decide)

/-! ### Valuations in the discrete valuation rings `𝒪_{X, ξ_j}` -/

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The valuation of a nonzero element of a discrete valuation ring, as a natural number. -/
private theorem coe_toNat_addVal {a : R} (ha : a ≠ 0) :
    ((IsDiscreteValuationRing.addVal R a).toNat : ℕ∞) = IsDiscreteValuationRing.addVal R a :=
  ENat.natCast_toNat ((IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr ha)

private theorem toNat_addVal_mul {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    (IsDiscreteValuationRing.addVal R (a * b)).toNat =
      (IsDiscreteValuationRing.addVal R a).toNat + (IsDiscreteValuationRing.addVal R b).toNat := by
  have h := IsDiscreteValuationRing.addVal_mul (R := R) (a := a) (b := b)
  rw [← coe_toNat_addVal ha, ← coe_toNat_addVal hb, ← coe_toNat_addVal (mul_ne_zero ha hb)] at h
  exact_mod_cast h

private theorem toNat_addVal_pow {a : R} (ha : a ≠ 0) (n : ℕ) :
    (IsDiscreteValuationRing.addVal R (a ^ n)).toNat =
      n * (IsDiscreteValuationRing.addVal R a).toNat := by
  have h := IsDiscreteValuationRing.addVal_pow (R := R) a n
  rw [← coe_toNat_addVal ha, ← coe_toNat_addVal (pow_ne_zero n ha), nsmul_eq_mul] at h
  exact_mod_cast h

private theorem dvd_iff_toNat_addVal_le {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    a ∣ b ↔ (IsDiscreteValuationRing.addVal R a).toNat ≤
      (IsDiscreteValuationRing.addVal R b).toNat := by
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, ← coe_toNat_addVal ha, ← coe_toNat_addVal hb]
  exact_mod_cast Iff.rfl

private theorem isUnit_of_toNat_addVal_eq_zero {a : R} (ha : a ≠ 0)
    (h : (IsDiscreteValuationRing.addVal R a).toNat = 0) : IsUnit a :=
  isUnit_of_dvd_one ((dvd_iff_toNat_addVal_le ha one_ne_zero).mpr (by omega))

private theorem one_le_toNat_addVal {a : R} (ha : a ≠ 0)
    (hm : a ∈ IsLocalRing.maximalIdeal R) : 1 ≤ (IsDiscreteValuationRing.addVal R a).toNat := by
  by_contra h
  exact (IsLocalRing.mem_maximalIdeal a).mp hm
    (isUnit_of_toNat_addVal_eq_zero ha (by omega))

private theorem notMem_maximalIdeal_mul_span_singleton {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (IsDiscreteValuationRing.addVal R x).toNat = (IsDiscreteValuationRing.addVal R y).toNat) :
    x ∉ IsLocalRing.maximalIdeal R * Ideal.span {y} := by
  intro hmem
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_mul_span_singleton.mp hmem
  have hr0 : r ≠ 0 := left_ne_zero_of_mul hx
  have := one_le_toNat_addVal hr0 hr
  rw [toNat_addVal_mul hr0 hy] at h
  omega

end Valuation

private theorem exists_pos_forall_mul_le_mul {ι : Type*} [Finite ι] (d e : ι → ℕ)
    (he : ∀ j, 1 ≤ e j) (j₀ : ι) (hd : 1 ≤ d j₀) : ∃ i, 1 ≤ d i ∧ ∀ j, d j * e i ≤ d i * e j := by
  cases nonempty_fintype ι
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j => (d j : ℚ) / (e j : ℚ)) ⟨j₀, Finset.mem_univ _⟩
  have hratio : ∀ j, d j * e i ≤ d i * e j := fun j => by
    have h := hi j (Finset.mem_univ _)
    have hej : (0 : ℚ) < e j := by exact_mod_cast he j
    have hei : (0 : ℚ) < e i := by exact_mod_cast he i
    rw [div_le_div_iff₀ hej hei] at h
    exact_mod_cast h
  refine ⟨i, Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, hratio⟩
  have h := hratio j₀
  rw [h0, zero_mul] at h
  exact (Nat.mul_pos hd (he i)).ne' (Nat.le_zero.mp h)

/-! ### The construction of the source's proof -/

/-- The germ at `x` of the pullback to `X` of an element of `A` is its image under
`A ⟶ 𝒪_{S, f x} ⟶ 𝒪_{X, x}`. -/
theorem germ_appTop_algebraMap (x : V.X) (a : V.A) :
    (V.X.presheaf.germ ⊤ x (Opens.mem_top x)).hom
        (V.f.appTop.hom ((Scheme.ΓSpecIso (.of V.A)).inv.hom a)) =
      (StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x).hom a :=
  (Scheme.Hom.germ_stalkMap_apply V.f ⊤ x (Opens.mem_top _) _).symm

/-- A component of the special fibre whose generic point lies on a closed subscheme lies in it. -/
private theorem componentInSource_subset_supportSet (I : V.X.IdealSheafData)
    (i : Fin V.numberOfComponents) (hi : componentGenericPoint V i ∈ I.support) :
    componentInSource V i ⊆ I.supportSet := by
  rintro _ ⟨q, hq, rfl⟩
  have hsp : componentGenericPoint V i ⤳ V.f.fiberι V.closedPoint q :=
    ((componentFiberGenericPoint_spec V i).specializes hq).map
      (V.f.fiberι V.closedPoint).continuous
  exact hsp.mem_closed I.support.isClosed (by simpa using hi)

/-- **A global function lying in `ℐ_J` at the generic points `ξ_j` on `J` is a section of `ℐ_J`**,
for an effective Cartier divisor `J` of a normal `X` contained in the special fibre: `J` is `(S_1)`
([Stacks, Tags 0B3S, 0346, 0B3M]) and its generic points are among the `ξ_j`. -/
private theorem mem_ker_subschemeι_app_of_germ_mem_stalkIdeal [IsNormal V.X]
    (J : V.X.IdealSheafData)
    [hJ : Stacks.Divisors.IsEffectiveCartierDivisor J]
    (hZs : J.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint)) (τ : Γ(V.X, ⊤))
    (hτ : ∀ j (hj : componentGenericPoint V j ∈ J.support),
      (V.X.presheaf.germ ⊤ (componentGenericPoint V j) (Opens.mem_top _)).hom τ ∈
        Stacks.AlgebraicGeometry.stalkIdeal J (componentGenericPoint V j) hj) :
    τ ∈ RingHom.ker (J.subschemeι.app ⊤).hom := by
  refine RingHom.mem_ker.mpr (eq_zero_of_germ_genericPoints_eq_zero_of_isEffectiveCartierDivisor
    V.X J hJ _ fun ζ hζ => ?_)
  obtain ⟨j, hj⟩ := exists_eq_componentGenericPoint_of_isGenericPoint V J hZs ζ
    ⟨⟨_, hζ⟩, isGenericPoint_closure⟩
  have key : ∀ (x : V.X) (hx : x ∈ J.support), x = componentGenericPoint V j →
      (V.X.presheaf.germ ⊤ x (Opens.mem_top x)).hom τ ∈
        Stacks.AlgebraicGeometry.stalkIdeal J x hx := by
    rintro x hx rfl
    exact hτ j hx
  exact (Scheme.Hom.germ_stalkMap_apply J.subschemeι ⊤ ζ (Opens.mem_top _) τ).symm.trans
    (RingHom.mem_ker.mp (key _ ζ.2 hj))

/-- **Krull's principal ideal theorem at a point `y` of `C_i` on no other component**: an element
of `ℐ_{J,y}` divisible by some `g ∈ 𝔪_y` not vanishing on `C_i` lies in `𝔪_y ℐ_{J,y}`. -/
private theorem mem_maximalIdeal_mul_stalkIdeal_of_dvd (J : V.X.IdealSheafData)
    [hJ : Stacks.Divisors.IsEffectiveCartierDivisor J]
    (hZs : J.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint)) (i : Fin V.numberOfComponents)
    (y : componentScheme V i) (hy : ∀ j, j ≠ i → componentι V i y ∉ componentInSource V j)
    (hx : componentι V i y ∈ J.support) {g t : V.X.presheaf.stalk (componentι V i y)}
    (hg : g ∈ IsLocalRing.maximalIdeal _) (hgC : ((componentι V i).stalkMap y).hom g ≠ 0)
    (ht : t ∈ Stacks.AlgebraicGeometry.stalkIdeal J _ hx) (hgt : g ∣ t) :
    t ∈ IsLocalRing.maximalIdeal _ * Stacks.AlgebraicGeometry.stalkIdeal J _ hx := by
  obtain ⟨h₀, hspan, -⟩ := Stacks.Divisors.exists_isRegular_stalkIdeal_eq_span J hJ _ hx
  rw [hspan] at ht ⊢
  refine IsLocalRing.mem_maximalIdeal_mul_span_of_dvd (ker_stalkMap_componentι_ne_bot V i y)
    ?_ hg (fun h => hgC (RingHom.mem_ker.mp h)) ht hgt
  rw [← hspan]
  exact ker_stalkMap_componentι_le_radical V J hZs i y hy hx

/-- **A section of `ℐ_J` generating `ℐ_J` at `ξ_i` and lying in `𝔪 ℐ_J` at a point of `C_i` gives
`deg(𝒞_{J/X}|_{C_i}) > 0`**: the section of `𝒞_{J/X}|_{C_i}` it defines is nonzero with a zero,
so part (2) of [Stacks, Tag 0B40] applies; the nonvanishing loci are compared along `C_i ⟶ X` by
[Stacks, Tag 0H78]. -/
private theorem invertibleCurveDegree_conormalOnComponent_pos_of_germ [IsNormal V.X]
    (J : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor J]
    (i : Fin V.numberOfComponents) (τ : Γ(V.X, ⊤)) (hτ : τ ∈ RingHom.ker (J.subschemeι.app ⊤).hom)
    (hξ : componentGenericPoint V i ∈ J.support)
    (hτξ : (V.X.presheaf.germ ⊤ (componentGenericPoint V i) (Opens.mem_top _)).hom τ ∉
      IsLocalRing.maximalIdeal _ * Stacks.AlgebraicGeometry.stalkIdeal J _ hξ)
    (y : componentScheme V i) (hy : componentι V i y ∈ J.support)
    (hτy : (V.X.presheaf.germ ⊤ (componentι V i y) (Opens.mem_top _)).hom τ ∈
      IsLocalRing.maximalIdeal _ * Stacks.AlgebraicGeometry.stalkIdeal J _ hy) :
    0 < invertibleCurveDegree (V.base.residueField V.closedPoint)
      (componentToSpecResidueField V i)
      (topologicalKrullDim_componentScheme_le_one_of_isNormal V i)
      (conormalOnComponent V J i) := by
  let c : (Stacks.Divisors.negativeTwist J).val.obj (op ⊤) :=
    (Stacks.Divisors.kernelIdealSheafIso J).inv.val.app (op ⊤)
      (Stacks.Divisors.mkKernelSection J τ hτ)
  have hc : ((Stacks.Divisors.idealInclusion J).val.app (op ⊤)).hom c = τ :=
    Stacks.Divisors.idealInclusion_val_app_kernelIdealSheafIso_inv J ⊤ _
  let L : SheafOfModules (structureSheafRing V.X.toRingedSpace) := Stacks.Divisors.negativeTwist J
  let LM : V.X.Modules := Stacks.SchemeModulesSpelling.toModules V.X L
  let s : L.sections := Stacks.SheafOfModules.sectionsOfTop (X := V.X.toRingedSpace) L c
  let σ := Stacks.SheafOfModules.modulePullbackSection (componentι V i).toLRSHom L s
  have hpre := Stacks.SheafOfModules.preimage_nonvanishingLocus (componentι V i).toLRSHom L s
  have hNV : ∀ x : V.X, x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := V.X.toRingedSpace) L s ↔
      (LM.presheaf.germ ⊤ x (Opens.mem_top x)).hom c ∉ Stacks.ModuleStalk.maximalSmul LM x := by
    intro x
    rw [Stacks.SchemeModulesSpelling.nonvanishingLocus_eq V.X L s]
    change x ∈ Stacks.Ample.nonvanishingLocus LM (s.eval (op ⊤)) ↔ _
    rw [Stacks.SheafOfModules.sectionsOfTop_eval_top]
    exact Iff.rfl
  obtain ⟨y0, hy0⟩ : componentGenericPoint V i ∈ Set.range (componentι V i) := by
    change componentGenericPoint V i ∈ Set.range (componentIdeal V i).subschemeι
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_componentIdeal]
    exact ⟨componentFiberGenericPoint V i, (componentFiberGenericPoint_spec V i).mem, rfl⟩
  have hy0NV : y0 ∈ Stacks.SheafOfModules.nonvanishingLocus
      (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V J i) σ := by
    rw [← hpre, Set.mem_preimage,
      show (componentι V i).toLRSHom.base y0 = componentGenericPoint V i from hy0, hNV]
    refine Stacks.ModuleStalk.Γgerm_notMem_maximalSmul (Stacks.Divisors.idealInclusion J) _
      (Stacks.AlgebraicGeometry.stalkIdeal J _ hξ)
      (fun U hx t => Stacks.Divisors.germ_idealInclusion_mem_stalkIdeal J _ hξ U hx t) c ?_
    change (V.X.presheaf.germ ⊤ _ (Opens.mem_top _)).hom
      (((Stacks.Divisors.idealInclusion J).val.app (op ⊤)).hom c) ∉ _
    rwa [hc]
  have hyNV : y ∉ Stacks.SheafOfModules.nonvanishingLocus
      (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V J i) σ := by
    rw [← hpre, Set.mem_preimage]
    change componentι V i y ∉ _
    rw [hNV, not_not]
    refine Stacks.ModuleStalk.Γgerm_mem_maximalSmul (Stacks.Divisors.idealInclusion J)
      (fun W => Stacks.Divisors.idealInclusion_app_injective J W) _
      (Stacks.AlgebraicGeometry.stalkIdeal J _ hy)
      (fun z hz => Stacks.Divisors.exists_stalkToLocalRing_idealInclusion_eq J _ hy z hz) c ?_
    change (V.X.presheaf.germ ⊤ _ (Opens.mem_top _)).hom
      (((Stacks.Divisors.idealInclusion J).val.app (op ⊤)).hom c) ∈ _
    rwa [hc]
  exact vanishingSectionDegreePos (V.base.residueField V.closedPoint) (componentScheme V i)
    (componentToSpecResidueField V i) inferInstance inferInstance
    (topologicalKrullDim_componentScheme_le_one_of_isNormal V i)
    (conormalOnComponent V J i) inferInstance σ
    (eval_top_ne_zero_of_mem_nonvanishingLocus _ σ hy0NV) ⟨y, hyNV⟩

/-- **The function `a^{d_i}` of the source's proof.** Let `a ∈ 𝔪` be nonzero, `e_j` the valuation
of `a` and `d_j` that of a local equation of `Z` in the discrete valuation ring `𝒪_{X, ξ_j}`, and
pick `i` with `d_i / e_i` maximal. Then `ξ_i ∈ Z`, and `a^{d_i}` lies in `ℐ_{e_i Z}` at every `ξ_j`
on `Z` but not in `𝔪 ℐ_{e_i Z}` at `ξ_i`. -/
private theorem exists_pow_mem_stalkIdeal_pow [IsNormal V.X] (I : V.X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor I] (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint)) {a : V.A} (ha0 : a ≠ 0)
    (ham : a ∈ V.maximalIdeal) :
    ∃ i : Fin V.numberOfComponents, ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      componentGenericPoint V i ∈ I.support ∧
      (∀ j (hj : componentGenericPoint V j ∈ (I ^ n).support),
        (StructureSheaf.toStalk V.A (V.f (componentGenericPoint V j)) ≫
          V.f.stalkMap (componentGenericPoint V j)).hom a ^ m ∈
            Stacks.AlgebraicGeometry.stalkIdeal (I ^ n) (componentGenericPoint V j) hj) ∧
      ∀ hi : componentGenericPoint V i ∈ (I ^ n).support,
        (StructureSheaf.toStalk V.A (V.f (componentGenericPoint V i)) ≫
          V.f.stalkMap (componentGenericPoint V i)).hom a ^ m ∉
            IsLocalRing.maximalIdeal _ *
              Stacks.AlgebraicGeometry.stalkIdeal (I ^ n) (componentGenericPoint V i) hi := by
  have hdim := topologicalKrullDim_component_eq_one_of_isEffectiveCartierDivisor V I hne hZs
  let ρ : ∀ x : V.X, V.A →+* V.X.presheaf.stalk x := fun x =>
    (StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x).hom
  have hDVR : ∀ j, IsDiscreteValuationRing (V.X.presheaf.stalk (componentGenericPoint V j)) :=
    fun j => isDiscreteValuationRing_stalk_componentGenericPoint V hdim j
  choose b hb0 hbspan hb1 using fun j =>
    Stacks.Divisors.exists_stalkIdeal_eq_span_or_eq_one I (componentGenericPoint V j)
  have haj : ∀ j, ρ (componentGenericPoint V j) a ≠ 0 := fun j h =>
    ha0 ((baseToStalk_injective V _).eq_iff.mp (h.trans (map_zero _).symm))
  let e : Fin V.numberOfComponents → ℕ := fun j =>
    (IsDiscreteValuationRing.addVal _ (ρ (componentGenericPoint V j) a)).toNat
  let d : Fin V.numberOfComponents → ℕ := fun j => (IsDiscreteValuationRing.addVal _ (b j)).toNat
  have he1 : ∀ j, 1 ≤ e j := fun j =>
    one_le_toNat_addVal (haj j)
      (baseToStalk_mem_maximalIdeal V _ (apply_componentGenericPoint V j) ham)
  obtain ⟨ζ, Zc, hζ⟩ := exists_isGenericPoint_subscheme I hne
  obtain ⟨j0, hj0⟩ := exists_eq_componentGenericPoint_of_isGenericPoint V I hZs ζ ⟨Zc, hζ⟩
  have hj0supp : componentGenericPoint V j0 ∈ I.support := by
    rw [← hj0]
    exact ζ.2
  have hd0 : 1 ≤ d j0 := one_le_toNat_addVal (hb0 j0)
    (Stacks.AlgebraicGeometry.stalkIdeal_le_maximalIdeal I _ hj0supp
      (hbspan j0 hj0supp ▸ Ideal.mem_span_singleton_self _))
  obtain ⟨i, hdi, hratio⟩ := exists_pos_forall_mul_le_mul d e he1 j0 hd0
  have hisupp : componentGenericPoint V i ∈ I.support := by
    by_contra h
    have : d i = 0 := by
      change (IsDiscreteValuationRing.addVal _ (b i)).toNat = 0
      rw [hb1 i h, IsDiscreteValuationRing.addVal_one]
      rfl
    omega
  have hsupp : (I ^ e i).support = I.support := I.support_pow _ (Nat.one_le_iff_ne_zero.mp (he1 i))
  refine ⟨i, e i, d i, he1 i, hdi, hisupp, fun j hj => ?_, fun hi => ?_⟩
  · have hxI : componentGenericPoint V j ∈ I.support := hsupp ▸ hj
    change ρ (componentGenericPoint V j) a ^ d i ∈ _
    rw [Stacks.AlgebraicGeometry.stalkIdeal_pow I _ _ hj hxI, hbspan j hxI,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      dvd_iff_toNat_addVal_le (pow_ne_zero _ (hb0 j)) (pow_ne_zero _ (haj j)),
      toNat_addVal_pow (hb0 j), toNat_addVal_pow (haj j), mul_comm (e i)]
    exact hratio j
  · change ρ (componentGenericPoint V i) a ^ d i ∉ _
    rw [Stacks.AlgebraicGeometry.stalkIdeal_pow I _ _ hi hisupp, hbspan i hisupp,
      Ideal.span_singleton_pow]
    refine notMem_maximalIdeal_mul_span_singleton (pow_ne_zero _ (haj i))
      (pow_ne_zero _ (hb0 i)) ?_
    rw [toNat_addVal_pow (haj i), toNat_addVal_pow (hb0 i)]
    exact mul_comm _ _

/-- In Situation [Stacks, Tag 0AX8] let `X` be normal and let `Z ⊆ X` be a nonempty effective
Cartier divisor contained set theoretically in the special fibre. Then there is a component `C_i`
of the special fibre with `C_i ⊆ Z` and `deg(𝒞_{Z/X}|_{C_i}) > 0`.

The proof is the source's. Let `a ∈ 𝔪` be the function of [Stacks, Tag 0AX9], with its points
`x_i ∈ C_i` and factorizations `a = g_i h_i` in `𝒪_{X, x_i}`. The local rings `𝒪_{X, ξ_i}` at the
generic points are discrete valuation rings; let `e_i` be the valuation of `a` and `d_i` that of
a local equation of `Z`, and pick `i` with `d_i / e_i` maximal (so `d_i > 0` and `C_i ⊆ Z`).
Then `a^{d_i}` vanishes at the generic points of `e_i Z`, all of which are generic points of
components of the special fibre, so it is a global section of `ℐ_{e_i Z}` because `e_i Z` is
`(S_1)` ([Stacks, Tags 0B3S, 0346, 0B3M]). Its restriction to `C_i` is nonzero, since `a^{d_i}`
generates `ℐ_{e_i Z}` at `ξ_i`, and vanishes at `x_i` by Krull's principal ideal theorem applied
to `g_i`; so `deg(𝒞_{e_i Z/X}|_{C_i}) > 0` by part (2) of [Stacks, Tag 0B40], and this degree is
`e_i · deg(𝒞_{Z/X}|_{C_i})` ([Stacks, Tags 02OP, 0B3P, 0AYX]). -/
@[stacks 0AXA "the precise clause: in Situation 0AX8 with X normal, for a nonempty effective \
Cartier divisor Z of X contained set theoretically in the special fibre, there is a component \
C_i of the special fibre with C_i contained in Z and deg(C_{Z/X}|_{C_i}) > 0; the \
dimension-one observation following Situation 0AX8, the section built from Lemma 0AX9 and part \
(2) of Tag 0B40 are all proved in the library"]
theorem exists_subset_invertibleCurveDegree_conormalOnComponent_pos [IsNormal V.X]
    (I : V.X.IdealSheafData) [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint)) :
    ∃ i : Fin V.numberOfComponents, componentInSource V i ⊆ I.supportSet ∧
      0 < invertibleCurveDegree (V.base.residueField V.closedPoint)
        (componentToSpecResidueField V i)
        (topologicalKrullDim_componentScheme_le_one_of_isNormal V i)
        (conormalOnComponent V I i) := by
  have hdim := topologicalKrullDim_component_eq_one_of_isEffectiveCartierDivisor V I hne hZs
  obtain ⟨a, ha0, ham, hpts⟩ := exists_ne_zero_mem_maximalIdeal_factorization V hdim
  obtain ⟨i, n, m, hn, hm, hi, hmem, hnot⟩ := exists_pow_mem_stalkIdeal_pow V I hne hZs ha0 ham
  have hCi := componentInSource_subset_supportSet V I i hi
  refine ⟨i, hCi, ?_⟩
  have hsupp : (I ^ n).support = I.support := I.support_pow n hn.ne'
  have hZs' : (I ^ n).supportSet ⊆ Set.range (V.f.fiberι V.closedPoint) :=
    Stacks.Divisors.supportSet_pow I hn ▸ hZs
  let τ : Γ(V.X, ⊤) := (V.f.appTop.hom ((Scheme.ΓSpecIso (.of V.A)).inv.hom a)) ^ m
  have hτgerm : ∀ x : V.X, (V.X.presheaf.germ ⊤ x (Opens.mem_top x)).hom τ =
      (StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x).hom a ^ m := by
    intro x
    simp only [τ, map_pow]
    rw [germ_appTop_algebraMap]
  have hτ := mem_ker_subschemeι_app_of_germ_mem_stalkIdeal V (I ^ n) hZs' τ fun j hj => by
    rw [hτgerm]
    exact hmem j hj
  obtain ⟨y, -, hyC, hynot, g, h', hgm, hgne, hfa⟩ := hpts i
  have hxI' : componentι V i y ∈ I.supportSet := hCi hyC
  have hxI : componentι V i y ∈ I.support := by simpa using hxI'
  have hy : componentι V i y ∈ (I ^ n).support := hsupp ▸ hxI
  have hξ : componentGenericPoint V i ∈ (I ^ n).support := hsupp ▸ hi
  have hpos := invertibleCurveDegree_conormalOnComponent_pos_of_germ V (I ^ n) i τ hτ hξ
    (by
      rw [hτgerm]
      exact hnot hξ) y hy
    (mem_maximalIdeal_mul_stalkIdeal_of_dvd V (I ^ n) hZs' i y hynot hy hgm hgne
      (Stacks.Divisors.germ_mem_stalkIdeal_of_mem_ker (I ^ n) ⊤ _ hy (Opens.mem_top _) τ hτ) (by
        rw [hτgerm, show (StructureSheaf.toStalk V.A (V.f (componentι V i y)) ≫
          V.f.stalkMap (componentι V i y)).hom a = g * h' from hfa]
        exact (dvd_mul_right g h').trans (dvd_pow_self _ hm.ne')))
  rw [invertibleCurveDegree_conormalOnComponent_pow V I i n] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)

/-- In Situation [Stacks, Tag 0AX8] with `X` normal, the conormal sheaf of a nonempty effective
Cartier divisor `Z ⊆ X` contained set theoretically in the special fibre is not trivial. If it
were, its restriction to the component `C_i ⊆ Z` provided by
`exists_subset_invertibleCurveDegree_conormalOnComponent_pos` would be isomorphic to `𝒪_{C_i}`
and so would have degree zero. -/
@[stacks 0AXA "the first clause: in Situation 0AX8 with X normal, the conormal sheaf of a \
nonempty effective Cartier divisor Z of X contained set theoretically in the special fibre is \
not trivial, derived from the precise clause since a trivial conormal sheaf restricts to a \
sheaf of degree zero on C_i"]
theorem not_isTrivial_conormalSheaf_of_nonempty [IsNormal V.X] (I : V.X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor I] (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint)) :
    ¬ SheafOfModules.IsTrivial I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      (Stacks.Conormal.conormalSheaf I.subschemeι) := by
  rintro ⟨e⟩
  obtain ⟨i, hCi, hdeg⟩ := exists_subset_invertibleCurveDegree_conormalOnComponent_pos V I hne hZs
  have hiso : conormalOnComponent V I i ≅
      SheafOfModules.unit (componentScheme V i).ringCatSheaf :=
    (conormalOnComponentIso V I i hCi).symm ≪≫
      Stacks.AmplePullback.modulePullbackIsoUnitModule (componentToDivisor V I i hCi) _ e
  rw [invertibleCurveDegree_eq_zero_of_iso_unit (V.base.residueField V.closedPoint)
    (componentToSpecResidueField V i) _ _ hiso] at hdeg
  exact hdeg.false

end AlgebraicGeometry.VanishingSituation

end
