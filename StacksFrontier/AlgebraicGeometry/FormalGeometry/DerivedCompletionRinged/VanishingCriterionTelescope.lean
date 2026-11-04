module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedLimits
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.TelescopeAway
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingFromComplete
public import StacksFrontier.CategoryTheory.Abelian.Telescope
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomLinearSource
public import StacksFrontier.Homology.DerivedComplete
public import StacksCore.Tactic.StacksAttribute

/-!
# The telescope criterion for the vanishing of derived internal Hom from a localization

Let `(𝒞, 𝒪)` be a ringed site, let `f` be a global section of `𝒪` and let `K ∈ D(𝒪)`.
[Stacks, Tag 0997] asserts the equivalence of

1. `R𝑆heafHom_𝒪(𝒪_f, K) = 0`,
2. `R𝑆heafHom_𝒪(L, K) = 0` for all `L` in `D(𝒪_f)`,
3. `T(K, f) = 0`,

where `T(K, f)` is a derived limit of the inverse system `⋯ → K --f--> K --f--> K` in `D(𝒪)`.
This file proves the equivalence of (1) and (3), in both directions.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHom_flip_map_globalSectionToEnd`: derived internal
  Hom into a fixed object carries multiplication by a global section **in the source** to
  multiplication by that section — the contravariant counterpart of
  `AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd`.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_awayTelescopeMap_comp_awayTelescopeSumIsoPi`:
  under `R𝑆heafHom_𝒪(∐ₙ 𝒪, K) ≅ ∏ₙ K` the map induced by the telescope differential is the
  Milnor difference map `1 - f·shift`.
* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_derivedAwayModule_iff_isDerivedCompleteAt`:
  the equivalence of (1) and (3) in [Stacks, Tag 0997], `R𝑆heafHom_𝒪(𝒪_f, K) = 0` if and only
  if `T(K, f) = 0`.

## Implementation notes

The `𝒪`-linearity of `R𝑆heafHom_𝒪(-, E)` is proved exactly as the covariant linearity of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomAdditive.lean` is: at the
level of internal Hom complexes the map induced by multiplication by a compatible family of
local sections of `𝒪` in the source is multiplication by that family, which is a computation on
local Hom components; the derived statement is then read off at a K-injective representative of
the target through `AlgebraicGeometry.RingedSite.derivedSheafHomComparison`, which is a
monomorphism, and transported to arbitrary objects in both variables.

The two transports are not the ones of the covariant case, because the variable carrying the
scalar is now the contravariant one. Varying the target moves the *component* of a fixed natural
endomorphism, which is `AlgebraicGeometry.RingedSite.natTrans_app_eq_smul_id_of_iso`; varying the
source conjugates the morphism being mapped, which is
`AlgebraicGeometry.RingedSite.map_op_smul_id_of_iso`, the opposite-category form of
`AlgebraicGeometry.RingedSite.map_smul_id_of_iso`.

### The two spellings of `𝒪^{⊕ ℕ}` and of `R𝑆heafHom_𝒪(𝒪, K)`

The comparison of the map induced by the telescope differential with `oneSubSmulShift K f` is
mathematically a one-line computation on each projection —
`Sigma.ι n ≫ (1 - f·shift) = Sigma.ι n - f ≫ Sigma.ι (n + 1)` read through the three additive
functors `single`, `DerivedCategory.Q` and `R𝑆heafHom_𝒪(-, K)` — but it is not expressible by a
single `rw`. The composites that occur mix two spellings of their intermediate objects which
agree only after unfolding `CategoryTheory.Functor.flip` and `CategoryTheory.ShortComplex.map`,
neither of which is reducible, so a rewrite inside such a composite reports that the target is
not type-correct and fails to find its pattern.
`AlgebraicGeometry.RingedSite.awaySequenceStructureSheafHomIso` and
`AlgebraicGeometry.RingedSite.awayTelescopeSumIsoPi` name the two identifications in the single
spelling the computation uses — the first because
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` is stated before the bifunctor is
flipped, the second because `AlgebraicGeometry.RingedSite.awaySigmaIsoPi` is stated at the term
of `AlgebraicGeometry.RingedSite.awayTelescopeComplex` — after which the rewrites go through.
The chain is split over three lemmas rather than one because `rw` has to try its pattern against
every composite in the goal, and on the whole equation at once that exceeds the elaboration
budget.

`CategoryTheory.Functor.ofSequence` is *not* an obstruction: its object field is reducible, so
`(awaySequence X a).obj n`
and `𝒪` are interchangeable in every position where they occur here, and
`AlgebraicGeometry.RingedSite.awaySequence_map_succ` rewrites its transition map to `a` inside a
motive that type-checks.

### The other implications of Tag 0997

Of the tag's three conditions the equivalence of (1) and (3) is proved here, the implication
(2) ⇒ (1) is `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_derivedAwayModule_of_forall`
of `VanishingCriterion.lean`, and (1) ⇒ (2) is
`AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_awayRestrictScalars_of_isZero` of
`VanishingCriterionCoextension.lean`.

The implication (1) ⇒ (2) uses Modules on Sites, Lemma 18.27.8,
`𝓗om_𝒪(R M, N) ≅ 𝓗om_{𝒪_f}(M, 𝓗om_𝒪(𝒪_f, N))` at the level of internal Hom *complexes*: that
is `AlgebraicGeometry.RingedSite.coextHomComplexIso` of `HomIntoCoextension.lean`, which is
[Stacks, Tag 0996(2)] at the complex level read on the slice sites. With it and the tag's
"in particular" — `coextIdempotentComplexIso`, whose epimorphism hypothesis is
`epi_toAwaySheaf` — (1) ⇒ (2) is the source's own argument, and no free resolution of `𝒪_f`
enters it: the telescope resolution is needed only for the equivalence with (3). The implication
(1) ⇒ (2) is the multiplicativity of the vanishing locus, the step from `T(K, f_i) = 0` to
`R𝑆heafHom_𝒪(𝒪_{f_S}, K) = 0` in [Stacks, Tag 099B].

## References

* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
* [Stacks Project, Tag 091S](https://stacks.math.columbia.edu/tag/091S)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] linearCatCenterRingSheaf

/- `Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian` is a second, definitionally
equal but syntactically different, `Abelian` instance on these sheaves of modules; letting it
into the derived categories here makes unification unfold both to compare them. -/
attribute [-instance] Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- A natural endomorphism of a functor which is multiplication by a scalar at one object is
multiplication by that scalar at every isomorphic object. -/
theorem natTrans_app_eq_smul_id_of_iso {R : Type*} [Semiring R] {C D : Type*} [Category C]
    [Category D] [Preadditive D] [Linear R D] {G : C ⥤ D} (θ : G ⟶ G) (r : R) {M N : C}
    (e : M ≅ N) (h : θ.app M = r • 𝟙 (G.obj M)) : θ.app N = r • 𝟙 (G.obj N) := by
  have hiso : IsIso (G.map e.hom) := (G.mapIso e).isIso_hom
  refine (cancel_epi (G.map e.hom)).mp ?_
  rw [θ.naturality e.hom, h, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    Category.comp_id]

/-- Derived internal Hom into the class of a K-injective complex carries multiplication by a
global section in the source to multiplication by that section. -/
private lemma derivedSheafHom_flip_map_globalSectionToEnd_model
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙ forget RingCat.{u}).sections)
    (A E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [E.IsKInjective] :
    ((derivedSheafHomBifunctor X).map
          (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
            𝟙 (DerivedCategory.Q.obj A)).op).app (DerivedCategory.Q.obj E) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj E)) := by
  have hQ : ∀ B : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      DerivedCategory.Q.map
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 B) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (DerivedCategory.Q.obj B) := fun B => by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  refine eq_smul_id_of_mono (c := (derivedSheafHomComparison X A E).hom) ?_
  rw [← hQ, derivedSheafHomComparison_naturality_id_target, homMap_globalSectionToEnd_left, hQ]

/-- **Derived internal Hom into a fixed object carries multiplication by a global section in the
source to multiplication by that section.** This is the `𝒪`-linearity of `R𝑆heafHom_𝒪(-, E)` in
its first variable, at the central endomorphisms given by compatible families of local sections
of `𝒪`; it is the contravariant counterpart of
`AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd`. -/
theorem derivedSheafHom_flip_map_globalSectionToEnd
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙ forget RingCat.{u}).sections)
    (A E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).map
          (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
            𝟙 A).op).app E =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (((derivedSheafHomBifunctor X).obj (op A)).obj E) := by
  have hmodel :
      ∀ (A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      ((derivedSheafHomBifunctor X).map
            (Stacks.SheafOfModules.globalSectionToEnd
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
              𝟙 (DerivedCategory.Q.obj A₀)).op).app E' =
        Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A₀))).obj E') := by
    intro A₀ E'
    have : (kInjectiveModel X E').IsKInjective := isKInjective_kInjectiveModel X E'
    exact natTrans_app_eq_smul_id_of_iso _ _ (kInjectiveModelIso X E')
      (derivedSheafHom_flip_map_globalSectionToEnd_model X a A₀ (kInjectiveModel X E'))
  exact map_op_smul_id_of_iso ((derivedSheafHomBifunctor X).flip.obj E) _
    (kInjectiveModelIso X A) (hmodel (kInjectiveModel X A) E)

end Derived


section Telescope

attribute [local instance] HasDerivedCategory.standard

variable [HasWeakSheafify X.J CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J CommRingCat] [HasSheafify X.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- On sections over `U`, `awaySmulUnit` is multiplication by the restriction of `f` to `U`. -/
theorem awaySmulUnit_apply (U : X.Cᵒᵖ)
    (x : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.obj U) :
    ((awaySmulUnit X h).val.app U).hom x = globalSectionVal h U • x :=
  awaySmul_app_apply X h _ U x

/-- The telescope short complex `∐ₙ 𝒪 ⟶ ∐ₙ 𝒪 ⟶ 𝒪_f` of sheaves of `𝒪`-modules. It is the
short complex whose short-exactness is `AlgebraicGeometry.RingedSite.awayTelescope_shortExact`. -/
abbrev awayTelescope :
    ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ShortComplex.mk (awayTelescopeMap X h)
    (Sigma.desc fun n : ℕ => colimit.ι (awayTelescopeSequence X h) n)
    (Stacks.MappingTelescope.telescope_general_hz (awayTelescopeSequence X h))

/-- The colimit of `𝒪 --f--> 𝒪 --f--> ⋯` is `𝒪_f`. -/
def awayTelescopeX₃Iso : (awayTelescope X h).X₃ ≅ awayModule X h :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitAwayModuleCocone X h (awaySmulUnit X h) fun U x => awaySmulUnit_apply X h U x)

/-- The telescope short complex, read in degree zero as a short complex of cochain complexes. -/
abbrev awayTelescopeComplex :
    ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  (awayTelescope X h).map
    (HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0)

omit [HasSheafify X.J AddCommGrpCat] in
/-- The telescope short complex, read in degree zero, is short exact. -/
theorem awayTelescopeComplex_shortExact : (awayTelescopeComplex X h).ShortExact :=
  (awayTelescope_shortExact X h).map_of_exact _

example : (DerivedCategory.triangleOfSES (awayTelescopeComplex_shortExact X h)).obj₁ =
    DerivedCategory.Q.obj (awayTelescopeComplex X h).X₁ := rfl

example : (DerivedCategory.triangleOfSES (awayTelescopeComplex_shortExact X h)).mor₁ =
    DerivedCategory.Q.map (awayTelescopeComplex X h).f := rfl

example : (DerivedCategory.triangleOfSES (awayTelescopeComplex_shortExact X h)).mor₂ =
    DerivedCategory.Q.map (awayTelescopeComplex X h).g := rfl

example : derivedAwayModule X h =
    DerivedCategory.Q.obj
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
        (awayModule X h)) := rfl

example : (awayTelescopeComplex X h).X₁ =
    (HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (∐ fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) := rfl

/-- The coproduct of `ℕ` copies of `𝒪`, read as a cofan indexed by `ULift ℕ`, is a coproduct:
reindexing along a bijection of index types. -/
def awaySigmaULiftCofanIsColimit :
    IsColimit (Cofan.mk (∐ fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n)
      (fun i : ULift.{u} ℕ =>
        show SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ _ from
          Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) i.down)) :=
  Cofan.IsColimit.mk _
    (fun s => Sigma.desc fun n : ℕ => s.inj (ULift.up n))
    (fun s i => Sigma.ι_desc _ i.down)
    (fun s m hm => by
      refine Sigma.hom_ext m (Sigma.desc fun n : ℕ => s.inj (ULift.up n)) fun n => ?_
      rw [Sigma.ι_desc]
      exact hm (ULift.up n))

/-- `𝒪^{⊕ ℕ}` is the coproduct of the terms of the diagram `𝒪 --f--> 𝒪 --f--> ⋯`. -/
def awayFreeIsoSigma :
    SheafOfModules.free.{u} (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ULift.{u} ℕ) ≅
      ∐ fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n :=
  IsColimit.coconePointUniqueUpToIso (SheafOfModules.isColimitFreeCofan.{u} (ULift.{u} ℕ))
    (awaySigmaULiftCofanIsColimit X h)

omit [HasWeakSheafify X.J CommRingCat] [HasSheafify X.J AddCommGrpCat] in
/-- The isomorphism `awayFreeIsoSigma` carries the `n`-th basis inclusion of `𝒪^{⊕ ℕ}` to the
inclusion of the `n`-th summand. -/
theorem ιFree_comp_awayFreeIsoSigma (n : ℕ) :
    SheafOfModules.ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ULift.up.{u} n) ≫
        (awayFreeIsoSigma X h).hom =
      Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk (ULift.up n))

/-- A limit fan on a constant family may be reindexed along a bijection of index types. -/
def isLimitConstFanReindex {C : Type*} [Category C] {α β : Type*} (e : α ≃ β) {K P : C}
    {q : β → (P ⟶ K)} (hq : IsLimit (Fan.mk P q)) :
    IsLimit (Fan.mk P fun a : α => q (e a)) := by
  refine Fan.IsLimit.mk _ (fun s => Fan.IsLimit.lift hq fun b => s.proj (e.symm b))
    (fun s a => ?_) (fun s m hm => ?_)
  · have hfac := Fan.IsLimit.fac hq (fun b => s.proj (e.symm b)) (e a)
    rw [e.symm_apply_apply] at hfac
    exact hfac
  · refine Fan.IsLimit.hom_ext hq _ _ fun b => ?_
    rw [Fan.IsLimit.fac]
    have hb := hm (e.symm b)
    rw [show (Fan.mk P fun a : α => q (e a)).proj (e.symm b) = q (e (e.symm b)) from rfl,
      e.apply_symm_apply] at hb
    exact hb

/-- The telescope's coproduct term, read as a complex in degree zero, is `𝒪^{⊕ ℕ}`. -/
def awayFreeComplexIsoSigma :
    freeComplex X (ULift.{u} ℕ) ≅ (awayTelescopeComplex X h).X₁ :=
  (HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).mapIso
    (awayFreeIsoSigma X h)

variable (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **`R𝑆heafHom_𝒪(∐ₙ 𝒪, K)` is the product of `ℕ` copies of `K`**, the `n`-th projection being
induced by the inclusion of the `n`-th summand. -/
def isLimitFanDerivedSheafHomAwaySigma :
    IsLimit (Fan.mk (((derivedSheafHomBifunctor X).flip.obj K).obj
        (op (DerivedCategory.Q.obj (awayTelescopeComplex X h).X₁)))
      fun n : ℕ => ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map
            ((HomologicalComplex.single
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) 0).map
                (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) n))).op ≫
        (derivedStructureSheafHomIso X K).hom) := by
  refine IsLimit.ofIsoLimit
    (isLimitConstFanReindex (K := K) Equiv.ulift.{u, 0}.symm
      (isLimitFanIsoComp (isLimitFanDerivedSheafHomFree X (ULift.{u} ℕ) K)
        (((derivedSheafHomBifunctor X).flip.obj K).mapIso
          (DerivedCategory.Q.mapIso (awayFreeComplexIsoSigma X h)).op)))
    (Cone.ext (Iso.refl _) fun j => ?_)
  obtain ⟨n⟩ := j
  have hι : freeComplexι X (ULift.{u} ℕ) (ULift.up n) ≫
      (awayFreeComplexIsoSigma X h).hom =
      (HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).map
        (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) n) :=
    (CategoryTheory.Functor.map_comp
        (HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0)
        (SheafOfModules.ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ULift.up.{u} n))
        (awayFreeIsoSigma X h).hom).symm.trans
      (congrArg
        (HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).map
        (ιFree_comp_awayFreeIsoSigma X h n))
  simp only [Fan.mk_π_app, Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Iso.op_hom]
  change ((derivedSheafHomBifunctor X).flip.obj K).map
        (DerivedCategory.Q.map (awayFreeComplexIsoSigma X h).hom).op ≫
      (((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map (freeComplexι X (ULift.{u} ℕ) (ULift.up n))).op ≫
        (derivedStructureSheafHomIso X K).hom) = _
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, ← Functor.map_comp, hι]
  rfl

omit [HasWeakSheafify X.J CommRingCat] [HasSheafify X.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Multiplication by a central scalar passes through the degree-zero single functor. -/
lemma single_map_smul_id
    (c : CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).map
        (c • 𝟙 M) =
      c • 𝟙 ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).obj M) := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  rcases eq_or_ne j 0 with rfl | hj
  · have hnat : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom ≫
          c.app M =
        c.app (((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).obj M).X 0) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom :=
      c.naturality _
    have hlhs : ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).map (c • 𝟙 M)).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom ≫ (c • 𝟙 M) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).inv :=
      HomologicalComplex.single_map_f_self _ _ _
    have hrhs : (c • 𝟙 ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).obj M)).f 0 =
        c.app (((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).obj M).X 0) := rfl
    rw [hlhs, hrhs, show (c • 𝟙 M : M ⟶ M) = c.app M from rfl, ← Category.assoc, hnat,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M j hj).eq_of_src _ _

/-- The derived category of sheaves of `𝒪`-modules has countable products. -/
instance hasProductsOfShape_nat_derived :
    HasProductsOfShape ℕ
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  hasProductsOfShape_nat_derivedCategory_ringSheaf.{u, u, u} X

/-- **`R𝑆heafHom_𝒪(∐ₙ 𝒪, K) ≅ ∏ₙ K`.** -/
def awaySigmaIsoPi :
    ((derivedSheafHomBifunctor X).flip.obj K).obj
        (op (DerivedCategory.Q.obj (awayTelescopeComplex X h).X₁)) ≅
      ∏ᶜ fun _ : ℕ => K :=
  IsLimit.conePointUniqueUpToIso (isLimitFanDerivedSheafHomAwaySigma X h K)
    (productIsProduct fun _ : ℕ => K)

omit [HasWeakSheafify X.J CommRingCat] in
/-- The `n`-th projection of `awaySigmaIsoPi` is induced by the inclusion of the `n`-th summand,
followed by the identification `R𝑆heafHom_𝒪(𝒪, K) ≅ K`. -/
@[reassoc]
lemma awaySigmaIsoPi_hom_π (n : ℕ) :
    (awaySigmaIsoPi X h K).hom ≫ Pi.π (fun _ : ℕ => K) n =
      ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map
            ((HomologicalComplex.single
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) 0).map
                (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) n))).op ≫
        (derivedStructureSheafHomIso X K).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimitFanDerivedSheafHomAwaySigma X h K)
    (productIsProduct fun _ : ℕ => K) ⟨n⟩

omit [HasWeakSheafify X.J CommRingCat] in
/-- Derived internal Hom into `K` carries multiplication by `f` on `𝒪` to multiplication by `f`,
read through the identification `R𝑆heafHom_𝒪(𝒪, K) = K`. -/
lemma derivedSheafHom_awaySmulUnit_comp_derivedStructureSheafHomIso :
    ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map (awaySmulUnit X h))).op ≫
        (derivedStructureSheafHomIso X K).hom =
      awaySmul X h • (derivedStructureSheafHomIso X K).hom := by
  have hsingle : (HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) 0).map (awaySmulUnit X h) =
      awaySmul X h • 𝟙 (structureSheafComplex X) :=
    single_map_smul_id X (awaySmul X h)
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  have hflip : ((derivedSheafHomBifunctor X).flip.obj K).map
        (awaySmul X h • 𝟙 (derivedStructureSheaf X)).op =
      awaySmul X h • 𝟙 (((derivedSheafHomBifunctor X).flip.obj K).obj
        (op (derivedStructureSheaf X))) :=
    derivedSheafHom_flip_map_globalSectionToEnd X (awayFamily X h) (derivedStructureSheaf X) K
  rw [hsingle, Functor.Linear.map_smul, CategoryTheory.Functor.map_id, hflip,
    Linear.smul_comp, Category.id_comp]

/-- **The identification `R𝑆heafHom_𝒪(𝒪, K) = K` at the `n`-th term of the telescope
diagram.**

Every term of `AlgebraicGeometry.RingedSite.awaySequence` *is* `𝒪`, but
`CategoryTheory.Functor.ofSequence` does not say so reducibly, and
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` is stated before the flip of the
derived internal Hom bifunctor is taken. Naming the identification in the spelling the telescope
computation uses keeps every composite below type-correct without unfolding either of those two
definitions, which is what a rewrite inside such a composite needs. -/
def awaySequenceStructureSheafHomIso (n : ℕ) :
    ((derivedSheafHomBifunctor X).flip.obj K).obj
        (op (DerivedCategory.Q.obj
          ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).obj
            ((awaySequence X (awaySmulUnit X h)).obj n)))) ≅ K :=
  derivedStructureSheafHomIso X K

/-- `R𝑆heafHom_𝒪(∐ₙ 𝒪, K) ≅ ∏ₙ K`, with the source spelled as the coproduct of the terms of the
telescope diagram rather than through `CategoryTheory.ShortComplex.map`. -/
def awayTelescopeSumIsoPi :
    ((derivedSheafHomBifunctor X).flip.obj K).obj
        (op (DerivedCategory.Q.obj
          ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).obj
            (awayTelescopeSum X (awaySmulUnit X h))))) ≅ ∏ᶜ fun _ : ℕ => K :=
  awaySigmaIsoPi X h K

omit [HasWeakSheafify X.J CommRingCat] in
/-- The `n`-th projection of `awayTelescopeSumIsoPi` is induced by the inclusion of the `n`-th
summand, followed by `awaySequenceStructureSheafHomIso`. -/
@[reassoc]
lemma awayTelescopeSumIsoPi_hom_π (n : ℕ) :
    (awayTelescopeSumIsoPi X h K).hom ≫ Pi.π (fun _ : ℕ => K) n =
      ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map
              (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) n))).op ≫
        (awaySequenceStructureSheafHomIso X h K n).hom :=
  awaySigmaIsoPi_hom_π X h K n

omit [HasWeakSheafify X.J CommRingCat] in
/-- The transition map of the telescope diagram is multiplication by `f`, so derived internal
Hom into `K` carries it to multiplication by `f` on `K`. -/
lemma derivedSheafHom_awaySequence_map_comp_awaySequenceStructureSheafHomIso (n : ℕ) :
    ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map
              ((awaySequence X (awaySmulUnit X h)).map (homOfLE n.le_succ)))).op ≫
        (awaySequenceStructureSheafHomIso X h K n).hom =
      awaySmul X h • (awaySequenceStructureSheafHomIso X h K (n + 1)).hom := by
  rw [awaySequence_map_succ]
  exact derivedSheafHom_awaySmulUnit_comp_derivedStructureSheafHomIso X h K

omit [HasSheafify X.J AddCommGrpCat] in
/-- **The telescope differential read by derived internal Hom into `K` on the `n`-th summand**:
the `n`-th inclusion minus the `n + 1`-st inclusion composed with the transition map. This is
the identity `e_n ↦ e_n - f e_{n + 1}` carried through the three additive functors
`HomologicalComplex.single`, `DerivedCategory.Q` and `R𝑆heafHom_𝒪(-, K)`. -/
lemma derivedSheafHom_awayTelescopeMap_comp_ι (n : ℕ) :
    ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map (awayTelescopeSumMap X (awaySmulUnit X h)))).op ≫
        ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map
              (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) n))).op =
      ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map
              (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) n))).op -
        ((derivedSheafHomBifunctor X).flip.obj K).map
            (DerivedCategory.Q.map ((HomologicalComplex.single
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) 0).map
                (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) (n + 1)))).op ≫
          ((derivedSheafHomBifunctor X).flip.obj K).map
            (DerivedCategory.Q.map ((HomologicalComplex.single
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) 0).map
                ((awaySequence X (awaySmulUnit X h)).map (homOfLE n.le_succ)))).op := by
  rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp, ← Functor.map_comp,
    awayTelescopeι_comp_awayTelescopeSumMap, Functor.map_sub, Functor.map_sub,
    CategoryTheory.op_sub, Functor.map_sub, Functor.map_comp, Functor.map_comp, op_comp]
  conv_lhs => rw [Functor.map_comp]

/-- The `n`-th projection of the map induced by the telescope differential, read through the
identification `R𝑆heafHom_𝒪(𝒪, K) = K`: the `n`-th projection minus `f` times the `n + 1`-st. -/
lemma derivedSheafHom_awayTelescopeMap_comp_ι_comp_homIso (n : ℕ) :
    (((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map (awayTelescopeSumMap X (awaySmulUnit X h)))).op ≫
        ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map
              (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) n))).op) ≫
        (awaySequenceStructureSheafHomIso X h K n).hom =
      ((derivedSheafHomBifunctor X).flip.obj K).map
            (DerivedCategory.Q.map ((HomologicalComplex.single
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) 0).map
                (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n) n))).op ≫
          (awaySequenceStructureSheafHomIso X h K n).hom -
        awaySmul X h • (((derivedSheafHomBifunctor X).flip.obj K).map
            (DerivedCategory.Q.map ((HomologicalComplex.single
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) 0).map
                (Sigma.ι (fun n : ℕ => (awaySequence X (awaySmulUnit X h)).obj n)
                  (n + 1)))).op ≫
          (awaySequenceStructureSheafHomIso X h K (n + 1)).hom) := by
  rw [derivedSheafHom_awayTelescopeMap_comp_ι, Preadditive.sub_comp, Category.assoc,
    derivedSheafHom_awaySequence_map_comp_awaySequenceStructureSheafHomIso, Linear.comp_smul]

/-- **The endomorphism of `∏ₙ K` induced by the telescope differential is the Milnor difference
map `1 - f·shift`.**

On the `n`-th projection the telescope differential is `e_n ↦ e_n - f e_{n + 1}`, so the map it
induces on `R𝑆heafHom_𝒪(∐ₙ 𝒪, K)` is the difference of the `n`-th projection and `f` times the
`n + 1`-st, derived internal Hom into `K` carrying multiplication by `f` on `𝒪` to
multiplication by `f` on `K`. -/
lemma derivedSheafHom_awayTelescopeMap_comp_awayTelescopeSumIsoPi :
    ((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map (awayTelescopeSumMap X (awaySmulUnit X h)))).op ≫
        (awayTelescopeSumIsoPi X h K).hom =
      (awayTelescopeSumIsoPi X h K).hom ≫ oneSubSmulShift K (awaySmul X h) := by
  refine Limits.Pi.hom_ext _ _ fun n => ?_
  rw [Category.assoc, Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub,
    Linear.comp_smul, awayTelescopeSumIsoPi_hom_π, awayTelescopeSumIsoPi_hom_π,
    ← Category.assoc, derivedSheafHom_awayTelescopeMap_comp_ι_comp_homIso]

/-- **[Stacks, Tag 0997], the equivalence of (1) and (3)**: the derived internal Hom
`R𝑆heafHom_𝒪(𝒪_f, K)` vanishes if and only if `T(K, f) = 0`.

Derived internal Hom into `K` carries the triangle of the telescope resolution of `𝒪_f` to a
distinguished triangle whose first vertex is `R𝑆heafHom_𝒪(𝒪_f, K)`, so that vertex vanishes
exactly when the second morphism of the triangle is invertible; under the identification
`R𝑆heafHom_𝒪(∐ₙ 𝒪, K) ≅ ∏ₙ K` that morphism is the Milnor difference map `1 - f·shift`, whose
invertibility is `T(K, f) = 0` by definition. -/
@[stacks 0997 "(1) ⇔ (3)"]
theorem isZero_derivedSheafHom_derivedAwayModule_iff_isDerivedCompleteAt :
    IsZero (((derivedSheafHomBifunctor X).obj (op (derivedAwayModule X h))).obj K) ↔
      IsDerivedCompleteAt K (awaySmul X h) := by
  have key : (awayTelescopeSumIsoPi X h K).inv ≫
        (((derivedSheafHomBifunctor X).flip.obj K).map
          (DerivedCategory.Q.map ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map (awayTelescopeSumMap X (awaySmulUnit X h)))).op ≫
          (awayTelescopeSumIsoPi X h K).hom) =
      oneSubSmulShift K (awaySmul X h) := by
    rw [derivedSheafHom_awayTelescopeMap_comp_awayTelescopeSumIsoPi, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [isZero_derivedSheafHom_derivedAwayModule_iff_isIso X h (awaySmulUnit X h)
      (fun U x => awaySmulUnit_apply X h U x) K, isDerivedCompleteAt_iff_isIso, ← key,
    isIso_comp_left_iff, isIso_comp_right_iff]

end Telescope



end AlgebraicGeometry.RingedSite

end
