module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.NearVanishingCofinal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientSystemNearVanishingTilde
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ComplementOpenExcision
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemFourTermLimit
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences

/-!
# Higher formal sections on a punctured spectrum: the sheaf side of Stacks 0EG4

Let `I`, `a` be ideals of a Noetherian ring `A`, `U = Spec(A) ∖ V(a)` and `F` a module on `U`
with `F ≅ M̃|_U`. Stacks 0EG4 compares the cohomology of `F` on `U`, and on the opens `V ⊆ U`
containing `U ∩ V(I)`, with the inverse limit of the cohomology of the quotients `F/IⁿF`. This
file reduces both of its assertions to statements about local cohomology of modules:

* on one open `V` whose image in `Spec A` is `Spec A ∖ V(J)`, the cone
  `H^i(V, F) → lim H^i(V, F/IⁿF)` is a limit cone as soon as the cone
  `H^{i+1}_{V(J)}(M) → lim H^{i+1}_{V(J)}(M/IⁿM)` is (`i ≥ 1`), respectively as soon as the cones
  in degrees `0` and `1` are, `{H⁰_{V(J)}(M/IⁿM)}` is Mittag-Leffler and `M` is `I`-adically
  complete (`i = 0`, through the four-term sequence of Stacks 0DWR and the five lemma for limits);
* the comparison `colim_V H^s(V, F) → lim_n H^s(U, F/IⁿF)` is defined by inverting the
  restriction isomorphisms `H^s(U, F/IⁿF) ≅ H^s(V, F/IⁿF)` (excision, `F/IⁿF` vanishing off
  `V(I)`), and it is an isomorphism as soon as the adic limit holds on the cofinal family of
  opens `U ∖ V(J)`, `J ⊆ J₀`, `V(J) ∩ V(I) = V(a)`.

Cohomology on an open `V` of `U` is `Stacks.LocalCohomology.complementOpenCohomology`, the right
derived functors of sections over `V` of `𝒪_U`-modules, read over `A`; for `V = U` it is
`H^i(U, -)`.

## Main definitions

* `Stacks.Algebraization.nearVanishingCohomology` — the diagram `V ↦ H^p(V, F)`.
* `Stacks.Algebraization.nearVanishingCocone` — its cocone to `lim_n H^p(U, F/IⁿF)`, whose
  descent is the comparison map of Stacks 0EG4.

## Main results

* `Stacks.Algebraization.nonempty_isLimit_complementOpenCohomology_of_one_le` and
  `Stacks.Algebraization.nonempty_isLimit_complementOpenCohomology_zero` — the adic limit on one
  open, from local cohomology.
* `Stacks.Algebraization.isIso_colimitDesc_nearVanishingCocone` — the colimit is computed on the
  cofinal opens.
* `Stacks.Algebraization.adicLimit_of_localCohomologyCones` — both assertions of Stacks 0EG4 from
  the local-cohomology cones.

## References

* [Stacks Project, Tag 0EG4](https://stacks.math.columbia.edu/tag/0EG4)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.LocalCohomology

universe u

namespace Stacks.Algebraization

/-- **A filtered colimit of modules is detected on a cofinal family.** Let `G` be a filtered
diagram of modules and `c` a cocone on it. If every index maps to an index `k` in a family `S` on
which the cocone map `G k ⟶ c.pt` is bijective, then the comparison `colimit G ⟶ c.pt` is an
isomorphism. -/
theorem isIso_colimitDesc_of_cofinal {J : Type u} [Category.{0} J] [IsFiltered J]
    {R : Type u} [Ring R] (G : J ⥤ ModuleCat.{u} R) (c : Cocone G) (S : J → Prop)
    (hS : ∀ j, ∃ k, S k ∧ Nonempty (j ⟶ k))
    (hbij : ∀ k, S k → Function.Bijective (c.ι.app k)) :
    IsIso (colimit.desc G c) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget (ModuleCat.{u} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, fun y ↦ ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
    obtain ⟨j, x, rfl⟩ := Concrete.colimit_exists_rep G z
    obtain ⟨k, hk, ⟨f⟩⟩ := hS j
    rw [← colimit.w G f, ConcreteCategory.comp_apply] at hz ⊢
    rw [← ConcreteCategory.comp_apply, colimit.ι_desc] at hz
    rw [(injective_iff_map_eq_zero _).1 (hbij k hk).1 _ hz, map_zero]
  · obtain ⟨k, hk, -⟩ := hS (IsFiltered.nonempty.some)
    obtain ⟨x, rfl⟩ := (hbij k hk).2 y
    exact ⟨colimit.ι G k x, by rw [← ConcreteCategory.comp_apply, colimit.ι_desc]⟩

/-! ### Transporting limit cones -/

/-- **A limit cone transported along an isomorphism of cones lying over an isomorphism of
diagrams**, after applying a functor. -/
theorem nonempty_isLimit_mapCone_of_iso {J C E : Type*} [Category J] [Category C] [Category E]
    {D D' : J ⥤ C} (α : D ≅ D') (c : Cone D) (c' : Cone D') (e : c.pt ≅ c'.pt)
    (w : ∀ j, c.π.app j ≫ α.hom.app j = e.hom ≫ c'.π.app j) (H : C ⥤ E)
    (h : Nonempty (IsLimit (H.mapCone c'))) : Nonempty (IsLimit (H.mapCone c)) := by
  obtain ⟨h⟩ := h
  let i : c ≅ (Cone.postcompose α.inv).obj c' := Cone.ext e fun j => by
    show c.π.app j = e.hom ≫ c'.π.app j ≫ α.inv.app j
    rw [← Category.assoc, ← w, Category.assoc, α.hom_inv_id_app, Category.comp_id]
  have h' : IsLimit (H.mapCone ((Cone.postcompose α.inv).obj c')) :=
    IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight α.symm H) _).symm h)
      (Functor.mapConePostcompose H).symm
  exact ⟨IsLimit.ofIsoLimit h' ((Cone.functoriality _ H).mapIso i).symm⟩

/-! ### The adic limit of the cohomology of one open, in terms of local cohomology -/

section OneOpen

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
  {F : (complementZeroLocus A a : Scheme).Modules} {M : ModuleCat.{u} A}
  (e : F ≅ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).obj
    ((tilde.functor (CommRingCat.of A)).obj M))

include e in
/-- The cone `F ⟶ F/IⁿF` of a module `F ≅ M̃|_U` on `U = Spec A ∖ V(a)` corresponds, after any
functor, to the image of the cone `M ⟶ M/IⁿM` under `N ↦ Ñ|_U`. -/
theorem nonempty_isLimit_mapCone_adicQuotientCone_iff_aux
    {E : Type*} [Category E] (H : (complementZeroLocus A a : Scheme).Modules ⥤ E)
    (h : Nonempty (IsLimit ((restrictTildeFunctor A a ⋙ H).mapCone
      (idealPowerQuotientCone.{u, u} I M)))) :
    Nonempty (IsLimit (H.mapCone (adicQuotientCone (idealSheafNearVanishing A I a) F))) :=
  nonempty_isLimit_mapCone_of_iso (quotientSystemNearVanishingTildeIso e) _
    ((restrictTildeFunctor A a).mapCone (idealPowerQuotientCone.{u, u} I M)) e
    (fun j => by
      induction j using Opposite.rec with
      | op n => exact adicProj_quotientSystemNearVanishingTildeIso_hom e n) H h

include e in
/-- **The adic limit on one open, in degrees `i ≥ 1`.** Let `V` be an open of
`U = Spec A ∖ V(a)` whose image in `Spec A` is `Spec A ∖ V(J)`, and let `F ≅ M̃|_U`. If
`H^{i+1}_{V(J)}(M) → lim H^{i+1}_{V(J)}(M/IⁿM)` is a limit cone, then so is
`H^i(V, F) → lim H^i(V, F/IⁿF)`: both are identified by `H^i(V, Ñ|_U) = H^{i+1}_{V(J)}(N)`,
naturally in the module `N` ([Stacks, Tag 0DWR]). -/
theorem nonempty_isLimit_complementOpenCohomology_of_one_le
    (V : (complementZeroLocus A a : Scheme).Opens) (J : Ideal A)
    (hV : (complementZeroLocus A a).ι ''ᵁ V = complementZeroLocus A J) (i : ℕ) (hi : 1 ≤ i)
    (h : Nonempty (IsLimit (localCohomologyAdicCone.{u, u} A
      (PrimeSpectrum.zeroLocus (J : Set A)) I ((i + 1 : ℕ) : ℤ) M))) :
    Nonempty (IsLimit ((complementOpenCohomology A a V i).mapCone
      (adicQuotientCone (idealSheafNearVanishing A I a) F))) := by
  refine nonempty_isLimit_mapCone_adicQuotientCone_iff_aux I a e _ ?_
  obtain ⟨h⟩ := h
  exact ⟨IsLimit.mapConeEquiv (complementOpenCohomologyTildeIso A a V J hV i ≪≫
    Stacks.LocalCohomologySequence.complementCohomologyBaseFunctorIso
      (A := CommRingCat.of A) J i hi).symm h⟩

omit [IsNoetherianRing A] in
/-- **An `I`-adically complete module is the limit of its quotients `M/IⁿM`.** -/
theorem nonempty_isLimit_idealPowerQuotientCone (hM : IsAdicComplete I M) :
    Nonempty (IsLimit (idealPowerQuotientCone.{u, u} I M)) := by
  refine (ModuleCat.InverseSystem.nonempty_isLimit_iff _).2 fun x hx => ?_
  have hcompat : ∀ {m n : ℕ} (h : m ≤ n),
      (idealPowerQuotientTower.{u, u} I M).map (homOfLE h).op (x n) = x m :=
    fun h => ModuleCat.InverseSystem.map_eq_of_succ x hx h
  choose f hf using fun n => Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule A M) (x n)
  obtain ⟨L, hL⟩ := hM.toIsPrecomplete.prec' f fun {m n} hmn => by
    show Submodule.Quotient.mk (f m) = Submodule.Quotient.mk (f n)
    rw [hf m, ← hcompat hmn, ← hf n]
    rfl
  refine ⟨L, fun n => ?_, fun y hy => ?_⟩
  · show Submodule.Quotient.mk L = x n
    rw [← hf n]
    exact (hL n).symm
  · let y' : M := y
    refine sub_eq_zero.1 (hM.toIsHausdorff.haus' (y' - L) fun n => ?_)
    show Submodule.Quotient.mk (y' - L) =
      (Submodule.Quotient.mk 0 : M ⧸ (I ^ n • ⊤ : Submodule A M))
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_zero, sub_eq_zero]
    show (idealPowerQuotientCone.{u, u} I M).π.app (op n) y = Submodule.Quotient.mk L
    rw [hy n, ← hf n]
    exact hL n

include e in
/-- **The adic limit on one open, in degree `0`.** Let `V` be an open of `U = Spec A ∖ V(a)` whose
image in `Spec A` is `Spec A ∖ V(J)`, and let `F ≅ M̃|_U` with `M` complete for `I`. If the cones
`H^k_{V(J)}(M) → lim H^k_{V(J)}(M/IⁿM)` are limit cones for `k = 0, 1` and the system
`{H⁰_{V(J)}(M/IⁿM)}` is Mittag-Leffler, then `Γ(V, F) → lim Γ(V, F/IⁿF)` is a limit cone.

This is the four-term sequence `0 → H⁰_{V(J)}(N) → N → Γ(V, Ñ|_U) → H¹_{V(J)}(N) → 0` of
[Stacks, Tag 0DWR], natural in `N`, and the five lemma for limits
(`ModuleCat.InverseSystem.nonempty_isLimit_of_fourTerm`). -/
theorem nonempty_isLimit_complementOpenCohomology_zero
    (V : (complementZeroLocus A a : Scheme).Opens) (J : Ideal A)
    (hV : (complementZeroLocus A a).ι ''ᵁ V = complementZeroLocus A J) (hM : IsAdicComplete I M)
    (h₀ : Nonempty (IsLimit (localCohomologyAdicCone.{u, u} A
      (PrimeSpectrum.zeroLocus (J : Set A)) I 0 M)))
    (h₁ : Nonempty (IsLimit (localCohomologyAdicCone.{u, u} A
      (PrimeSpectrum.zeroLocus (J : Set A)) I 1 M)))
    (hML : IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} A
      (PrimeSpectrum.zeroLocus (J : Set A)) I 0 M)) :
    Nonempty (IsLimit ((complementOpenCohomology A a V 0).mapCone
      (adicQuotientCone (idealSheafNearVanishing A I a) F))) := by
  refine nonempty_isLimit_mapCone_adicQuotientCone_iff_aux I a e _ ?_
  suffices h : Nonempty (IsLimit ((Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor
      (A := CommRingCat.of A) J 0).mapCone (idealPowerQuotientCone.{u, u} I M))) by
    obtain ⟨h⟩ := h
    exact ⟨IsLimit.mapConeEquiv (complementOpenCohomologyTildeIso A a V J hV 0).symm h⟩
  let α := Stacks.LocalCohomologySequence.localCohomologyZeroToSelf (A := CommRingCat.of A) J
  let β := Stacks.LocalCohomologySequence.selfToComplementSections (A := CommRingCat.of A) J
  let γ := Stacks.LocalCohomologySequence.complementSectionsToLocalCohomologyOne
    (A := CommRingCat.of A) J
  let D := idealPowerQuotientTower.{u, u} I M
  let c := idealPowerQuotientCone.{u, u} I M
  have hex : ∀ N : ModuleCat.{u} A, Function.Injective (α.app N) ∧
      Function.Exact (α.app N) (β.app N) ∧ Function.Exact (β.app N) (γ.app N) ∧
      Function.Surjective (γ.app N) := by
    intro N
    have h3 := Stacks.LocalCohomologySequence.exact_lowDegree_natural (A := CommRingCat.of A) J N
    refine ⟨(ModuleCat.mono_iff_injective _).1
        (Stacks.LocalCohomologySequence.mono_localCohomologyZeroToSelf_app
          (A := CommRingCat.of A) J N), ?_, ?_,
      (ModuleCat.epi_iff_surjective _).1
        (Stacks.LocalCohomologySequence.epi_complementSectionsToLocalCohomologyOne_app
          (A := CommRingCat.of A) J N)⟩
    · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (h3.exact 0)
    · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (h3.exact 1)
  obtain ⟨hc₁⟩ := h₀
  obtain ⟨hc₂⟩ := nonempty_isLimit_idealPowerQuotientCone I hM
  obtain ⟨hc₄⟩ := h₁
  exact ModuleCat.InverseSystem.nonempty_isLimit_of_fourTerm
    (Functor.whiskerLeft D α) (Functor.whiskerLeft D β) (Functor.whiskerLeft D γ)
    (fun n => (hex _).1) (fun n => (hex _).2.1) (fun n => (hex _).2.2.1) hML
    (localCohomologyAdicCone.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) I 0 M) c
    ((Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor
      (A := CommRingCat.of A) J 0).mapCone c)
    (localCohomologyAdicCone.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) I 1 M)
    (α.app M) (β.app M) (γ.app M) (hex M).2.1 (hex M).2.2.1 (hex M).2.2.2
    (fun n => (α.naturality _).symm) (fun n => (β.naturality _).symm)
    (fun n => (γ.naturality _).symm) hc₁ hc₂ hc₄

end OneOpen

/-! ### Cohomology over the neighbourhoods of the formal locus -/

section NearVanishing

variable (A : Type u) [CommRing A] (I a : Ideal A)

/-- The restriction of sections from an open `V` to itself is the identity. -/
theorem sectionsOnOpenRestriction_refl (X : RingedSpace.{u, u}) (V : Opens X) :
    sectionsOnOpenRestriction X (le_refl V) = 𝟙 _ := by
  ext G x
  let y : G.val.obj (op V) := x
  exact PresheafOfModules.congr_map_apply G.val (show (homOfLE (le_refl V)).op = 𝟙 _ from rfl) y
    |>.trans (by rw [PresheafOfModules.map_id]; rfl)

/-- The restriction `H^p(V, -) ⟶ H^p(V', -)` for opens `V' ≤ V` of `U = Spec A ∖ V(a)`. -/
def complementOpenCohomologyRestriction {V V' : (complementZeroLocus A a : Scheme).Opens}
    (h : V' ≤ V) (p : ℕ) :
    complementOpenCohomology A a V p ⟶ complementOpenCohomology A a V' p :=
  Functor.whiskerRight
    (NatTrans.rightDerived (sectionsOnOpenRestriction _ h) p)
    (ModuleCat.restrictScalars (complementTopScalars a))

/-- For opens `V'' ≤ V' ≤ V`, the restrictions `H^p(V, -) ⟶ H^p(V', -) ⟶ H^p(V'', -)` compose
to the restriction `H^p(V, -) ⟶ H^p(V'', -)`. -/
theorem complementOpenCohomologyRestriction_comp
    {V V' V'' : (complementZeroLocus A a : Scheme).Opens} (h : V' ≤ V) (h' : V'' ≤ V') (p : ℕ) :
    complementOpenCohomologyRestriction A a h p ≫ complementOpenCohomologyRestriction A a h' p =
      complementOpenCohomologyRestriction A a (h'.trans h) p :=
  (Functor.whiskerRight_comp _ _ _).symm.trans
    (congrArg (fun t => Functor.whiskerRight t (ModuleCat.restrictScalars (complementTopScalars a)))
      ((NatTrans.rightDerived_comp _ _ p).symm.trans
        (congrArg (fun t => NatTrans.rightDerived t p) (sectionsOnOpenRestriction_comp _ h h'))))

/-- The restriction `H^p(V, -) ⟶ H^p(V, -)` from an open `V` to itself is the identity. -/
theorem complementOpenCohomologyRestriction_refl (V : (complementZeroLocus A a : Scheme).Opens)
    (p : ℕ) : complementOpenCohomologyRestriction A a (le_refl V) p = 𝟙 _ := by
  refine (congrArg
      (fun t => Functor.whiskerRight t (ModuleCat.restrictScalars (complementTopScalars a)))
      ((congrArg (fun t => NatTrans.rightDerived t p) (sectionsOnOpenRestriction_refl _ V)).trans
        (NatTrans.rightDerived_id _ p))).trans ?_
  rfl

variable (F : (complementZeroLocus A a : Scheme).Modules) (p : ℕ)

/-- **The diagram `V ↦ H^p(V, F)` over the neighbourhoods `V ⊆ U` of the formal locus
`U ∩ V(I)`**, with the restriction maps; its colimit is `colim_V H^p(V, F)`. -/
def nearVanishingCohomology : OpensNearVanishing A I a ⥤ ModuleCat.{u} A where
  obj V := (complementOpenCohomology A a V.openSet p).obj F
  map g := (complementOpenCohomologyRestriction A a g.down p).app F
  map_id V := by
    rw [complementOpenCohomologyRestriction_refl]
    rfl
  map_comp g g' := by
    rw [← NatTrans.comp_app, complementOpenCohomologyRestriction_comp]

/-- The restriction from `U` to a neighbourhood `V` of the formal locus is an isomorphism on the
cohomology of `F / IⁿF`, which vanishes off `V(I)`. -/
instance isIso_complementOpenCohomologyRestriction_quotient (V : OpensNearVanishing A I a)
    (n : ℕᵒᵖ) :
    IsIso ((complementOpenCohomologyRestriction A a (le_top : V.openSet ≤ ⊤) p).app
      ((quotientSystemNearVanishing A I a F).obj n)) := by
  have h := isIso_rightDerived_sectionsOnOpenRestriction_of_subsingleton
    (complementZeroLocus A a : Scheme) (V := V.openSet)
    (W := (idealSheafNearVanishing A I a).support.compl)
    (by
      refine eq_top_iff.2 fun x _ => ?_
      by_cases hx : x ∈ ((idealSheafNearVanishing A I a).support : Set _)
      · exact Or.inl (support_idealSheafNearVanishing_le A I a V hx)
      · exact Or.inr hx)
    ((quotientSystemNearVanishing A I a F).obj n)
    (fun O hO => subsingleton_adicQuotientSystem_sections_of_le_compl_support _ F n.unop hO) p
  change IsIso ((ModuleCat.restrictScalars (complementTopScalars a)).map _)
  infer_instance

/-- **The comparison map of Stacks 0EG4**, from a neighbourhood: `H^p(V, F) ⟶ H^p(V, F/IⁿF)`,
followed by the inverse of the restriction isomorphism `H^p(U, F/IⁿF) ≅ H^p(V, F/IⁿF)`, as a cone
over the tower `n ↦ H^p(U, F/IⁿF)`. -/
def nearVanishingCone (V : OpensNearVanishing A I a) :
    Cone (quotientSystemNearVanishing A I a F ⋙ complementOpenCohomology A a ⊤ p) where
  pt := (complementOpenCohomology A a V.openSet p).obj F
  π :=
    { app n := (complementOpenCohomology A a V.openSet p).map
          (adicProj (idealSheafNearVanishing A I a) F n) ≫
        inv ((complementOpenCohomologyRestriction A a (le_top : V.openSet ≤ ⊤) p).app
          ((quotientSystemNearVanishing A I a F).obj n))
      naturality m n g := by
        have hnat := (complementOpenCohomologyRestriction A a (le_top : V.openSet ≤ ⊤) p).naturality
          ((quotientSystemNearVanishing A I a F).map g)
        have key : inv ((complementOpenCohomologyRestriction A a (le_top : V.openSet ≤ ⊤) p).app
              ((quotientSystemNearVanishing A I a F).obj m)) ≫
            (complementOpenCohomology A a ⊤ p).map ((quotientSystemNearVanishing A I a F).map g) =
            (complementOpenCohomology A a V.openSet p).map
              ((quotientSystemNearVanishing A I a F).map g) ≫
            inv ((complementOpenCohomologyRestriction A a (le_top : V.openSet ≤ ⊤) p).app
              ((quotientSystemNearVanishing A I a F).obj n)) := by
          rw [IsIso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id,
            Category.comp_id]
        change 𝟙 _ ≫ _ = _ ≫ (complementOpenCohomology A a ⊤ p).map
          ((quotientSystemNearVanishing A I a F).map g)
        rw [Category.id_comp, Category.assoc, key, ← Category.assoc, ← Functor.map_comp,
          adicProj_comp_map] }

/-- The cocone on `V ↦ H^p(V, F)` with point `lim_n H^p(U, F/IⁿF)`. -/
def nearVanishingCocone :
    Cocone (nearVanishingCohomology A I a F p) where
  pt := limit (quotientSystemNearVanishing A I a F ⋙ complementOpenCohomology A a ⊤ p)
  ι :=
    { app V := limit.lift _ (nearVanishingCone A I a F p V)
      naturality V W g := by
        refine limit.hom_ext fun n => ?_
        let Fn := (quotientSystemNearVanishing A I a F).obj n
        let ρ := complementOpenCohomologyRestriction A a g.down p
        let rV := complementOpenCohomologyRestriction A a (le_top : V.openSet ≤ ⊤) p
        let rW := complementOpenCohomologyRestriction A a (le_top : W.openSet ≤ ⊤) p
        have hrW : rW.app Fn = rV.app Fn ≫ ρ.app Fn := by
          rw [← NatTrans.comp_app, complementOpenCohomologyRestriction_comp]
        have : IsIso (ρ.app Fn) := by
          have : IsIso (rV.app Fn ≫ ρ.app Fn) := hrW ▸ inferInstance
          exact IsIso.of_isIso_comp_left (rV.app Fn) (ρ.app Fn)
        have hρ := ρ.naturality (adicProj (idealSheafNearVanishing A I a) F n)
        change (ρ.app F ≫ limit.lift _ (nearVanishingCone A I a F p W)) ≫ _ =
          (limit.lift _ (nearVanishingCone A I a F p V) ≫ 𝟙 _) ≫ _
        refine (Category.assoc _ _ _).trans ?_
        rw [Category.comp_id, limit.lift_π]
        refine (congrArg (fun t => ρ.app F ≫ t) (limit.lift_π _ _)).trans ?_
        change ρ.app F ≫ (complementOpenCohomology A a W.openSet p).map
            (adicProj (idealSheafNearVanishing A I a) F n) ≫ inv (rW.app Fn) =
          (complementOpenCohomology A a V.openSet p).map
            (adicProj (idealSheafNearVanishing A I a) F n) ≫ inv (rV.app Fn)
        have hinv : inv (rW.app Fn) = inv (ρ.app Fn) ≫ inv (rV.app Fn) :=
          IsIso.inv_eq_of_hom_inv_id (by
            rw [hrW, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id])
        rw [hinv, ← Category.assoc, ← hρ, Category.assoc, IsIso.hom_inv_id_assoc] }

/-- **A neighbourhood on which the adic limit holds gives an isomorphism to the formal side.** If
`H^p(V, F) → lim H^p(V, F/IⁿF)` is a limit cone, the component at `V` of the cocone
`nearVanishingCocone` is an isomorphism: it differs from that cone by the restriction isomorphisms
`H^p(U, F/IⁿF) ≅ H^p(V, F/IⁿF)`. -/
theorem isIso_nearVanishingCocone_ι_app (V : OpensNearVanishing A I a)
    (h : Nonempty (IsLimit ((complementOpenCohomology A a V.openSet p).mapCone
      (adicQuotientCone (idealSheafNearVanishing A I a) F)))) :
    IsIso ((nearVanishingCocone A I a F p).ι.app V) := by
  obtain ⟨h⟩ := h
  let D := quotientSystemNearVanishing A I a F
  let r := complementOpenCohomologyRestriction A a (le_top : V.openSet ≤ ⊤) p
  have : IsIso (Functor.whiskerLeft D r) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun n =>
      isIso_complementOpenCohomologyRestriction_quotient A I a F p V n
  let β : D ⋙ complementOpenCohomology A a V.openSet p ≅ D ⋙ complementOpenCohomology A a ⊤ p :=
    (asIso (Functor.whiskerLeft D r)).symm
  have hlim : IsLimit (nearVanishingCone A I a F p V) :=
    IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv β _).symm h)
      (Cone.ext (Iso.refl _) fun n => by
        show (complementOpenCohomology A a V.openSet p).map
            (adicProj (idealSheafNearVanishing A I a) F n) ≫ β.hom.app n =
          𝟙 _ ≫ (complementOpenCohomology A a V.openSet p).map
            (adicProj (idealSheafNearVanishing A I a) F n) ≫ inv (r.app (D.obj n))
        rw [Category.id_comp]
        congr 1
        exact IsIso.eq_inv_of_hom_inv_id
          (congrArg (fun t => NatTrans.app t n) (asIso (Functor.whiskerLeft D r)).hom_inv_id))
  exact (IsLimit.nonempty_isLimit_iff_isIso_lift (limit.isLimit _)).1 ⟨hlim⟩

/-- **The colimit over the neighbourhoods is computed on a cofinal family.** Let `J₀` be an ideal
with `V(J₀) ∩ V(I) = V(a)`. If for every `J ⊆ J₀` with `V(J) ∩ V(I) = V(a)` the adic limit
`H^p(V_J, F) → lim H^p(V_J, F/IⁿF)` holds on `V_J = U ∖ V(J)`, then
`colim_V H^p(V, F) → lim H^p(U, F/IⁿF)` is an isomorphism. -/
theorem isIso_colimitDesc_nearVanishingCocone (J₀ : Ideal A)
    (hJ₀ : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A))
    (h : ∀ (J : Ideal A), J ≤ J₀ →
      ∀ hJ : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A),
      Nonempty (IsLimit ((complementOpenCohomology A a
        (OpensNearVanishing.ofIdeal A I a J hJ.le).openSet p).mapCone
          (adicQuotientCone (idealSheafNearVanishing A I a) F)))) :
    IsIso (colimit.desc (nearVanishingCohomology A I a F p) (nearVanishingCocone A I a F p)) := by
  refine isIso_colimitDesc_of_cofinal _ _
    (fun V => ∃ (J : Ideal A) (_ : J ≤ J₀)
      (hJ : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A)), V = OpensNearVanishing.ofIdeal A I a J hJ.le)
    (fun V => ?_) (fun V hV => ?_)
  · obtain ⟨J, hJle, hJ, hV⟩ := OpensNearVanishing.exists_ofIdeal_le hJ₀ V
    exact ⟨_, ⟨J, hJle, hJ, rfl⟩, hV⟩
  · obtain ⟨J, hJle, hJ, rfl⟩ := hV
    exact (ConcreteCategory.isIso_iff_bijective _).1
      (isIso_nearVanishingCocone_ι_app A I a F p _ (h J hJle hJ))

end NearVanishing

/-! ### Assembly from the local-cohomology cones -/

section Assembly

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
  {F : (complementZeroLocus A a : Scheme).Modules} {M : ModuleCat.{u} A}
  (e : F ≅ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).obj
    ((tilde.functor (CommRingCat.of A)).obj M))

omit [IsNoetherianRing A] in
/-- If a cone `c` over a diagram `D` is a limit cone, the canonical map `c.pt ⟶ limit D` is an
isomorphism. -/
theorem isIso_limit_lift_of_nonempty_isLimit {J C : Type*} [Category J] [Category C] {D : J ⥤ C}
    [HasLimit D] {c : Cone D} (h : Nonempty (IsLimit c)) : IsIso (limit.lift D c) := by
  exact (IsLimit.nonempty_isLimit_iff_isIso_lift (limit.isLimit D)).1 h

include e in
/-- **Stacks 0EG4 from its local-cohomology inputs.** Let `F ≅ M̃|_U` on `U = Spec A ∖ V(a)` with
`M` complete for `I`, and let `s ≥ 0`. Suppose that

* for `i ≤ s` the cones `H^i_{V(a)}(M) → lim H^i_{V(a)}(M/IⁿM)` are limit cones and
  `{H⁰_{V(a)}(M/IⁿM)}` is Mittag-Leffler (Theorem 0EIE);
* there is `J₀` with `V(J₀) ∩ V(I) = V(a)` such that for every `J ⊆ J₀` with
  `V(J) ∩ V(I) = V(a)` the cones `H^i_{V(J)}(M) → lim H^i_{V(J)}(M/IⁿM)` are limit cones for
  `i ≤ s + 1`, and `{H⁰_{V(J)}(M/IⁿM)}` is Mittag-Leffler (Lemmas 0EFL and 0EG0).

Then `H^i(U, F) → lim H^i(U, F/IⁿF)` is an isomorphism for `i < s` and
`colim_V H^s(V, F) → lim H^s(U, F/IⁿF)` is an isomorphism. -/
theorem adicLimit_of_localCohomologyCones (hM : IsAdicComplete I M) (s : ℕ)
    (hα : ∀ i : ℕ, i ≤ s → Nonempty (IsLimit (localCohomologyAdicCone.{u, u} A
      (PrimeSpectrum.zeroLocus (a : Set A)) I (i : ℤ) M)))
    (hαML : IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} A
      (PrimeSpectrum.zeroLocus (a : Set A)) I 0 M))
    (J₀ : Ideal A)
    (hJ₀ : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A))
    (hβ : ∀ J : Ideal A, J ≤ J₀ →
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A) →
      (∀ i : ℕ, i ≤ s + 1 → Nonempty (IsLimit (localCohomologyAdicCone.{u, u} A
        (PrimeSpectrum.zeroLocus (J : Set A)) I (i : ℤ) M))) ∧
      IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} A
        (PrimeSpectrum.zeroLocus (J : Set A)) I 0 M)) :
    (∀ i : ℕ, i < s →
      IsIso (limit.lift (quotientSystemNearVanishing A I a F ⋙ complementOpenCohomology A a ⊤ i)
        ((complementOpenCohomology A a ⊤ i).mapCone
          (adicQuotientCone (idealSheafNearVanishing A I a) F)))) ∧
    IsIso (colimit.desc (nearVanishingCohomology A I a F s) (nearVanishingCocone A I a F s)) := by
  refine ⟨fun i hi => isIso_limit_lift_of_nonempty_isLimit ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact nonempty_isLimit_complementOpenCohomology_zero I a e ⊤ a
        (Scheme.Opens.ι_image_top _) hM (hα 0 (Nat.zero_le _)) (hα 1 hi) hαML
    · exact nonempty_isLimit_complementOpenCohomology_of_one_le I a e ⊤ a
        (Scheme.Opens.ι_image_top _) i hi0 (hα (i + 1) hi)
  · refine isIso_colimitDesc_nearVanishingCocone A I a F s J₀ hJ₀ fun J hJle hJ => ?_
    obtain ⟨hlim, hML⟩ := hβ J hJle hJ
    have hV : (complementZeroLocus A a).ι ''ᵁ
        (OpensNearVanishing.ofIdeal A I a J hJ.le).openSet = complementZeroLocus A J :=
      complementZeroLocus_ι_image_preimage A a (hJ ▸ Set.inter_subset_left)
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · exact nonempty_isLimit_complementOpenCohomology_zero I a e _ J hV hM
        (hlim 0 (Nat.zero_le _)) (hlim 1 le_rfl) hML
    · exact nonempty_isLimit_complementOpenCohomology_of_one_le I a e _ J hV s hs0
        (hlim (s + 1) le_rfl)

end Assembly

end Stacks.Algebraization

end
