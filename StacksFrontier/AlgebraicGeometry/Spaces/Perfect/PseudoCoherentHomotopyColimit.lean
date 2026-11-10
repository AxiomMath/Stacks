module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.HomotopyColimitSupported
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectHomVanishingWindow
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherent objects on an algebraic space as homotopy colimits of perfect ones

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S` and
let `K` be an object of `D(𝒪_X)`.  Then `K` is pseudo-coherent if and only if `K = hocolim Kₙ`
for a system of perfect objects `Kₙ` such that `τ_{≥-n}Kₙ ⟶ τ_{≥-n}K` is an isomorphism for
every `n` ([Stacks, Tag 0DKB]).

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_approximation_of_isPseudoCoherent`: a
  pseudo-coherent object of `D(𝒪_X)` is approximated from any degree by a perfect object, at any
  model of `D(𝒪_X)`; this is the triple `(|X|, K, m)` of Stacks 08HI, for which approximation
  holds by Stacks 08HJ and 08HP.
* `AlgebraicGeometry.Space.exists_perfect_factorization`: the induction step of the source's
  proof.
* `AlgebraicGeometry.Space.isPseudoCoherent_iff_exists_isHomotopyColimitWith`:
  **Stacks 0DKB**.

## Implementation notes

**The proof** is the source's.  For `(1) ⟹ (2)`, choose an approximation `K₁ ⟶ K` of
`(|X|, K, -2)` (Stacks 08HP).  Given a perfect `Kₙ ⟶ K`, Stacks 09MB gives a window `[a, b]` of
degrees in which vanishing of the cohomology of an object of `D_QCoh(𝒪_X)` forbids nonzero maps
out of `Kₙ`; an approximation `Kₙ₊₁ ⟶ K` of `(|X|, K, min(a - 1, -n - 2))` has a cone `C` in
`D_QCoh(𝒪_X)` with no cohomology from degree `a` on, so `Kₙ ⟶ K ⟶ C` vanishes and `Kₙ ⟶ K`
factors through `Kₙ₊₁` (Stacks 0149).  That `K` is the derived colimit of the tower is Stacks 0CRK
for the cohomology functors, which commute with countable direct sums: the system `Hⁱ(Kₙ)` is
eventually constant with value `Hⁱ(K)`
(`AlgebraicGeometry.Space.isHomotopyColimitWith_of_eventually_isIso_homology_modules`).  For
`(2) ⟹ (1)`, a perfect object is pseudo-coherent (Stacks 08G8), and the cone of `Kₙ ⟶ K` has no
cohomology in degrees `≥ -n`, so `K` is `(-n)`-pseudo-coherent by Stacks 08FV, for every `n`.

**Indexing.** The source indexes the system from `1`; here it is indexed by `ℕ` from `0`, and
the member at index `n` is the source's `K_{n+1}`.  So the condition at index `n` is that
`τ_{≥-(n+1)}Kₙ ⟶ τ_{≥-(n+1)}K` is an isomorphism, which is the source's condition verbatim.

**Derived colimits.** "`K = hocolim Kₙ`" is
`CategoryTheory.Pretriangulated.IsHomotopyColimitWith F K c`: there is a distinguished triangle
`⊕ Kₙ ⟶ ⊕ Kₙ ⟶ K ⟶` whose first map is `1 - fₙ` and whose second map restricts to `cₙ` on the
`n`-th summand (Stacks 090Z).  The truncation condition is imposed on these coprojections `cₙ`,
which are the maps `Kₙ ⟶ K` the source refers to.  The direct sum `⊕ Kₙ` exists because the
`𝒪_X`-modules form a Grothendieck abelian category
(`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`).

**The model of `D(𝒪_X)`** is arbitrary.  Approximation by perfect complexes (Stacks 08HI, 08HJ)
is defined at the standard model, so the approximations of Stacks 08HP are produced there and
carried to the given model along the comparison of the two models,
`StacksDraft.DerivedModel.modelEquiv`, which identifies the localization functors and the
cohomology functors.  Everything else — Stacks 09MB, the distinguished triangles, the
truncations and the derived colimit — is read at the given model directly.

## References

* [Stacks Project, Tag 0DKB](https://stacks.math.columbia.edu/tag/0DKB)
* [Stacks Project, Tag 08HP](https://stacks.math.columbia.edu/tag/08HP)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08HJ](https://stacks.math.columbia.edu/tag/08HJ)
* [Stacks Project, Tag 09MB](https://stacks.math.columbia.edu/tag/09MB)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 0149](https://stacks.math.columbia.edu/tag/0149)
* [Stacks Project, Tag 0CRK](https://stacks.math.columbia.edu/tag/0CRK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StacksDraft.DerivedModel

universe w w₁ w₂ u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] pointTopology smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

/-- The cohomology of the comparison of a morphism across two models of the derived category is
the cohomology of the morphism, conjugated by the comparison of the cohomology functors. -/
theorem homologyFunctor_map_modelEquiv_functor_map {C : Type*} [Category C] [Abelian C]
    (h₁ : HasDerivedCategory.{w₁} C) (h₂ : HasDerivedCategory.{w₂} C)
    {E F : @DerivedCategory C _ _ h₁} (f : E ⟶ F) (i : ℤ) :
    (@DerivedCategory.homologyFunctor C _ _ h₂ i).map ((modelEquiv h₁ h₂).functor.map f) =
      (modelHomologyFunctorIso h₁ h₂ i).hom.app E ≫
        (@DerivedCategory.homologyFunctor C _ _ h₁ i).map f ≫
          (modelHomologyFunctorIso h₁ h₂ i).inv.app F := by
  have h := (modelHomologyFunctorIso h₁ h₂ i).hom.naturality f
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- The open subspace attached to the empty complement of `|X|` has quasi-compact inclusion: every
base change of it has no points, hence is quasi-compact (Stacks 03E4).  This is what makes the
whole space `T = |X|` admissible in Stacks 08HJ. -/
theorem isQuasiCompact_ι_openSubspacesOrderIso_symm_compl_univ :
    IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X hX).symm
        ⟨(Set.univ : Set (points B S hS X))ᶜ, isClosed_univ.isOpen_compl⟩).1.ι := by
  intro Z hZ' _ g
  set U := (openSubspacesOrderIso B S hS X hX).symm
    ⟨(Set.univ : Set (points B S hS X))ᶜ, isClosed_univ.isOpen_compl⟩ with hU
  have hP := isAlgebraicSpace_pullback B S hS g U.1.ι hZ' U.2.1 hX
  refine isQuasiCompactSpace_of_compactSpace_points B S hS hP ?_
  have : IsEmpty (points B S hS (pullback g U.1.ι)) := ⟨fun p => by
    have hr : Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) =
        (Set.univ : Set (points B S hS X))ᶜ :=
      range_openSubspacesOrderIso_symm B S hS X hX Set.univ isClosed_univ
    have hmem : pointsMap B S hS _ U.1.ι (pointsMap B S hS _ (pullback.snd g U.1.ι) p) ∈
        Set.range (pointsMap B S hS _ U.1.ι) := ⟨_, rfl⟩
    rw [hr] at hmem
    exact hmem (Set.mem_univ _)⟩
  infer_instance

/-! ### Derived colimits in `D(𝒪_X)` -/

/-- `D(𝒪_X)` has countable direct sums, at any model: the `𝒪_X`-modules form a Grothendieck
abelian category (`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`), in the universe of
the structure sheaf. -/
theorem hasColimitsOfShape_discrete_nat_derivedCategory_modules
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)] :
    HasColimitsOfShape (Discrete ℕ) (DerivedCategory (Modules.{u, u} B S hS X hX)) :=
  have := isGrothendieckAbelian_modules B S hS X hX
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    (Modules.{u, u} B S hS X hX) (ULift.{u} ℕ)
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)

/-- **A derived colimit in `D(𝒪_X)` detected by cohomology**, at any model.  Let
`F : ℕ ⥤ D(𝒪_X)` be a system and let `cₙ : Kₙ ⟶ K` be maps compatible with the transition maps.
If in every degree `i` the maps `Hⁱ(cₙ)` are isomorphisms for all large `n`, then `K` is the
derived colimit of the system with coprojections `cₙ`.

This is Stacks 0CRK for the cohomology functors, which commute with countable direct sums, as in
`Stacks.DerivedColimit.isHomotopyColimitWith_of_eventually_isIso_homology`; that statement asks
the category to be Grothendieck abelian in the universe of its morphisms, whereas the
`𝒪_X`-modules on the small étale site are Grothendieck abelian in the universe of the structure
sheaf, one below. -/
theorem isHomotopyColimitWith_of_eventually_isIso_homology_modules
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (F : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X hX)) [HasCoproduct F.obj]
    {K : DerivedCategory (Modules.{u, u} B S hS X hX)}
    (c : ∀ n, F.obj n ⟶ K)
    (hc : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) = c n)
    (hiso : ∀ i : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).map (c n))) :
    IsHomotopyColimitWith F K c := by
  have := isGrothendieckAbelian_modules B S hS X hX
  have : HasColimitsOfShape ℕ (Modules.{u, u} B S hS X hX) :=
    hasColimitsOfShape_of_equivalence (AsSmall.equiv.{0, 0, u}).symm
  have : HasExactColimitsOfShape ℕ (Modules.{u, u} B S hS X hX) :=
    HasExactColimitsOfShape.of_domain_equivalence (Modules.{u, u} B S hS X hX)
      (AsSmall.equiv.{0, 0, u}).symm
  obtain ⟨C, p, q, hT⟩ :=
    distinguished_cocone_triangle (Stacks.CountableCoproducts.oneSubShift F)
  have hone : Stacks.CountableCoproducts.oneSubShift F ≫ Sigma.desc c = 0 := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [← Category.assoc, Stacks.CountableCoproducts.ι_oneSubShift, Preadditive.sub_comp,
      Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc, hc, sub_self, comp_zero]
  obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ _ hT (Sigma.desc c) hone
  have hpb : ∀ n, Sigma.ι F.obj n ≫ p ≫ b = c n := fun n => by
    have := congrArg (fun φ => Sigma.ι F.obj n ≫ φ) hb
    simpa using this.symm
  have hbiso : IsIso b := by
    rw [DerivedCategory.isIso_iff]
    intro i
    let H := DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i
    have : PreservesColimitsOfShape (Discrete ℕ) H :=
      have := Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor
        (Modules.{u, u} B S hS X hX)
        (J := ULift.{u} ℕ) i
      preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
    obtain ⟨e, he⟩ := exists_iso_colimit_of_isHomotopyColimit F H p q hT
    obtain ⟨N, hN⟩ := hiso i
    let cK : Cocone (F ⋙ H) :=
      { pt := H.obj K
        ι :=
          { app := fun n => H.map (c n)
            naturality := fun m n f => by
              have h := Stacks.DerivedColimit.comp_eq_of_le F c hc (leOfHom f)
              rw [show homOfLE (leOfHom f) = f from Subsingleton.elim _ _] at h
              simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
                Functor.const_obj_map, Category.comp_id, ← H.map_comp, h] } }
    have hev : (F ⋙ H).IsEventuallyConstantFrom N := by
      intro n f
      have hle : N ≤ n := leOfHom f
      have h₁ := hN N le_rfl
      have h₂ := hN n hle
      have hcomp : H.map (F.map f) ≫ H.map (c n) = H.map (c N) := by
        rw [← H.map_comp, show f = homOfLE hle from Subsingleton.elim _ _,
          Stacks.DerivedColimit.comp_eq_of_le F c hc hle]
      have : IsIso (H.map (F.map f) ≫ H.map (c n)) := by rw [hcomp]; exact h₁
      exact (isIso_comp_right_iff (H.map (F.map f)) (H.map (c n))).1 this
    have : IsIso (cK.ι.app N) := hN N le_rfl
    let hcK : IsColimit cK := hev.isColimitOfIsIso cK
    have hfac : e.hom ≫ H.map b = colimit.desc (F ⋙ H) cK := by
      refine colimit.hom_ext fun n => ?_
      rw [← Category.assoc, he, ← H.map_comp, Category.assoc, hpb, colimit.ι_desc]
    have : IsIso (colimit.desc (F ⋙ H) cK) :=
      inferInstanceAs (IsIso ((colimit.isColimit (F ⋙ H)).coconePointUniqueUpToIso hcK).hom)
    exact (isIso_comp_left_iff e.hom (H.map b)).1 (by rw [hfac]; infer_instance)
  exact (IsHomotopyColimitWith.of_iso ⟨p, q, hT, fun _ => rfl⟩ (asIso b)).congr_coprojections
    fun n => by simpa using hpb n

/-- **Approximation of a pseudo-coherent object by a perfect one**, at any model of `D(𝒪_X)`.
On a quasi-compact and quasi-separated algebraic space, a pseudo-coherent `K` admits, for every
`m`, a perfect `P` and a map `P ⟶ K` which is an isomorphism on cohomology in degrees `> m` and a
surjection in degree `m`: approximation holds for the triple `(|X|, K, m)` of Stacks 08HI, by
Stacks 08HJ and 08HP.

The approximation of Stacks 08HP is produced at the standard model, at an object representing
`K` there, and carried to the given model along `StacksDraft.DerivedModel.modelEquiv`. -/
theorem exists_isPerfect_approximation_of_isPseudoCoherent
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [hD : HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (K : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hK : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherent K) (m : ℤ) :
    ∃ P : DerivedCategory (Modules.{u, u} B S hS X hX),
      (smallEtaleRingedSite B S hS X hX).IsPerfect P ∧
        ∃ α : P ⟶ K,
          (∀ i : ℤ, m < i →
            IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) m).map α) := by
  let std := HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
  let Φ := modelEquiv std hD
  obtain ⟨Kc, hKc, ⟨eK⟩⟩ := hK
  let K₀ := (@DerivedCategory.Q _ _ _ std).obj Kc
  have hK₀qc := derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X hX K₀
    ⟨Kc, hKc, ⟨Iso.refl _⟩⟩
  obtain ⟨r, hr⟩ := approximationByPerfectComplexes_of_qcqs B S hS hZ X hX hqc hqs Set.univ
    isClosed_univ (isQuasiCompact_ι_openSubspacesOrderIso_symm_compl_univ B S hS X hX)
  obtain ⟨P, hP, -, α, hαi, hαe⟩ := hr ⟨K₀, hK₀qc⟩ m ⟨Kc, hKc (m - r), ⟨Iso.refl _⟩⟩
    (fun _ _ => Set.subset_univ _)
  obtain ⟨Pc, hPc, ⟨eP⟩⟩ := hP
  let eK' : Φ.functor.obj K₀ ≅ K := (modelCompQIso std hD).app Kc ≪≫ eK
  refine ⟨Φ.functor.obj P, ⟨Pc, hPc, ⟨((modelCompQIso std hD).app Pc).symm ≪≫
    Φ.functor.mapIso eP⟩⟩, Φ.functor.map α ≫ eK'.hom, ?_, ?_⟩
  · intro i hi
    rw [Functor.map_comp, homologyFunctor_map_modelEquiv_functor_map]
    have := hαi i hi
    infer_instance
  · rw [Functor.map_comp, homologyFunctor_map_modelEquiv_functor_map]
    exact epi_comp' (epi_comp' (@IsIso.epi_of_iso _ _ _ _ _
        (Iso.isIso_hom ((modelHomologyFunctorIso std hD m).app P)))
      (epi_comp' hαe (@IsIso.epi_of_iso _ _ _ _ _
        (Iso.isIso_inv ((modelHomologyFunctorIso std hD m).app K₀)))))
      (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom
        ((@DerivedCategory.homologyFunctor _ _ _ hD m).mapIso eK')))

/-- **Stacks 08JL, second assertion, at any model of `D(𝒪_X)`**: a pseudo-coherent object of
`D(𝒪_X)` has quasi-coherent cohomology sheaves.  The cohomology sheaves of the object are those
of a pseudo-coherent complex representing it, which are quasi-coherent by
`AlgebraicGeometry.Space.derivedCategoryB_of_isPseudoCoherent_unconditional` at the standard
model. -/
theorem derivedCategoryB_of_isPseudoCoherent_anyModel
    [hD : HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hE : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherent E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))) E := by
  let std := HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
  obtain ⟨Kc, hKc, ⟨e⟩⟩ := hE
  have h₀ := derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X hX
    ((@DerivedCategory.Q _ _ _ std).obj Kc) ⟨Kc, hKc, ⟨Iso.refl _⟩⟩
  intro i
  exact (qcohModules B S hS ⟨X, hX⟩).prop_of_iso
    (((modelHomologyFunctorIso std hD i).app ((@DerivedCategory.Q _ _ _ std).obj Kc)).symm ≪≫
      (@DerivedCategory.homologyFunctor _ _ _ hD i).mapIso
        ((modelCompQIso std hD).app Kc ≪≫ e)) (h₀ i)

/-- In a distinguished triangle of `D(𝒪_X)`, at any model, whose first two vertices have
quasi-coherent cohomology, so does the third: quasi-coherence on the small étale site is a weak
Serre class. -/
theorem derivedCategoryB_quasicoherent_obj₃_anyModel
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (Tri : Triangle (DerivedCategory (Modules.{u, u} B S hS X hX)))
    (hTri : Tri ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS X hX)))
    (h₁ : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))) Tri.obj₁)
    (h₂ : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))) Tri.obj₂) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))) Tri.obj₃ :=
  DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _
    (isWeakSerre_quasicoherentSheaves_smallEtaleRingedSite B S hS X hX) Tri.rotate
    (rot_of_distTriang Tri hTri) h₂
    (DerivedCategoryB.derivedCategoryB_shift_mem _
      (isWeakSerre_quasicoherentSheaves_smallEtaleRingedSite B S hS X hX)
      1 h₁)

/-- **The induction step of the proof of Stacks 0DKB.**  On a quasi-compact and quasi-separated
algebraic space, let `K` be pseudo-coherent.  Every map `f` from a perfect object `P` to `K`
factors as `P ⟶ Q ⟶ K` through a perfect `Q` whose map to `K` is an isomorphism on cohomology in
every degree `≥ a`, for any prescribed `a`.

Following the source: take a window `[a₀, b₀]` for `P` as in Stacks 09MB and an approximation
`β : Q ⟶ K` of `(|X|, K, min(a₀ - 1, a - 1))`.  The cone `C` of `β` lies in `D_QCoh(𝒪_X)` and has
no cohomology from degree `min(a₀ - 1, a - 1)` on, so `Hom(P, C) = 0`; the composite
`P ⟶ K ⟶ C` vanishes and `f` factors through `β` (Stacks 0149). -/
theorem exists_perfect_factorization
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    {K : DerivedCategory (Modules.{u, u} B S hS X hX)}
    (hK : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherent K)
    {P : DerivedCategory (Modules.{u, u} B S hS X hX)}
    (hP : (smallEtaleRingedSite B S hS X hX).IsPerfect P) (f : P ⟶ K) (a : ℤ) :
    ∃ (Q : DerivedCategory (Modules.{u, u} B S hS X hX)) (g : P ⟶ Q) (β : Q ⟶ K),
      (smallEtaleRingedSite B S hS X hX).IsPerfect Q ∧ g ≫ β = f ∧
        ∀ i : ℤ, a ≤ i →
          IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).map β) := by
  obtain ⟨a₀, b₀, -, hwin⟩ :=
    exists_window_subsingleton_hom_of_isPerfect B S hS hZ X hX hqc hqs P hP
  obtain ⟨Q, hQ, β, hβi, hβe⟩ := exists_isPerfect_approximation_of_isPseudoCoherent B S hS hZ X
    hX hqc hqs K hK (min (a₀ - 1) (a - 1))
  obtain ⟨C, v, w', hT₃⟩ := distinguished_cocone_triangle β
  have hQqc := derivedCategoryB_of_isPseudoCoherent_anyModel B S hS X hX Q
    (RingedSite.isPseudoCoherent_of_isPerfect_general _ hQ)
  have hKqc := derivedCategoryB_of_isPseudoCoherent_anyModel B S hS X hX K hK
  have hCqc := derivedCategoryB_quasicoherent_obj₃_anyModel B S hS X hX _ hT₃ hQqc hKqc
  have hC : Subsingleton (P ⟶ C) := hwin C (fun i => hCqc i) fun i hi _ =>
    CategoryTheory.isZero_homology_obj₃_of_distinguished (min (a₀ - 1) (a - 1)) _ hT₃ hβi hβe i
      (by omega)
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT₃ f (@Subsingleton.elim _ hC _ _)
  exact ⟨Q, g, β, hQ, hg.symm, fun i hi => hβi i (by omega)⟩

/-! ### The tower of approximations -/

/-- A member of the tower of the proof of Stacks 0DKB at index `n`: a perfect object with a map to
`K` which is an isomorphism on cohomology in degrees `≥ -(n + 1)`. -/
private structure Stage [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (K : DerivedCategory (Modules.{u, u} B S hS X hX)) (n : ℕ) where
  obj : DerivedCategory (Modules.{u, u} B S hS X hX)
  perfect : (smallEtaleRingedSite B S hS X hX).IsPerfect obj
  toTarget : obj ⟶ K
  isIso : ∀ i : ℤ, -((n : ℤ) + 1) ≤ i →
    IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).map toTarget)

/-- The first member of the tower: an approximation of `(|X|, K, -2)`. -/
private theorem exists_stage_zero
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    {K : DerivedCategory (Modules.{u, u} B S hS X hX)}
    (hK : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherent K) :
    Nonempty (Stage B S hS X hX K 0) := by
  obtain ⟨P, hP, α, hαi, -⟩ :=
    exists_isPerfect_approximation_of_isPseudoCoherent B S hS hZ X hX hqc hqs K hK (-2)
  exact ⟨⟨P, hP, α, fun i hi => hαi i (by omega)⟩⟩

/-- The induction step of the tower: the map of a member to `K` factors through the next. -/
private theorem exists_stage_succ
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    {K : DerivedCategory (Modules.{u, u} B S hS X hX)}
    (hK : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherent K) (n : ℕ)
    (s : Stage B S hS X hX K n) :
    ∃ s' : Stage B S hS X hX K (n + 1), ∃ g : s.obj ⟶ s'.obj, g ≫ s'.toTarget = s.toTarget := by
  obtain ⟨Q, g, β, hQ, hg, hβ⟩ :=
    exists_perfect_factorization B S hS hZ X hX hqc hqs hK s.perfect s.toTarget (-((n : ℤ) + 2))
  exact ⟨⟨Q, hQ, β, fun i hi => hβ i (by push_cast at hi; omega)⟩, g, hg⟩

/-! ### Stacks 0DKB -/

/-- **Stacks 0DKB.**  Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated
algebraic space over `S` and let `K ∈ D(𝒪_X)`.  The following are equivalent:
1. `K` is pseudo-coherent;
2. `K = hocolim Kₙ` where `Kₙ` is perfect and `τ_{≥-n}Kₙ ⟶ τ_{≥-n}K` is an isomorphism for all
   `n`.

The model of `D(𝒪_X)` is arbitrary.  The system is `F : ℕ ⥤ D(𝒪_X)`, indexed from `0`, its
member `F.obj n` being the source's `K_{n+1}`; so the truncation condition at index `n` is in
degree `-(n + 1)`.  The maps `Kₙ ⟶ K` are the coprojections `c n` of the derived colimit
(`CategoryTheory.Pretriangulated.IsHomotopyColimitWith`), whose direct sum `⊕ Kₙ` exists because
the `𝒪_X`-modules form a Grothendieck abelian category. -/
@[stacks 0DKB]
theorem isPseudoCoherent_iff_exists_isHomotopyColimitWith
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (K : DerivedCategory (Modules.{u, u} B S hS X hX)) :
    haveI := hasColimitsOfShape_discrete_nat_derivedCategory_modules B S hS X hX
    (smallEtaleRingedSite B S hS X hX).IsPseudoCoherent K ↔
      ∃ (F : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X hX)) (c : ∀ n, F.obj n ⟶ K),
        (∀ n, (smallEtaleRingedSite B S hS X hX).IsPerfect (F.obj n)) ∧
          (∀ n : ℕ,
            IsIso ((DerivedCategory.TStructure.t.truncGE (-((n : ℤ) + 1))).map (c n))) ∧
            IsHomotopyColimitWith F K c := by
  have := hasColimitsOfShape_discrete_nat_derivedCategory_modules B S hS X hX
  constructor
  · intro hpc
    obtain ⟨s₀⟩ := exists_stage_zero B S hS hZ X hX hqc hqs hpc
    let step := exists_stage_succ B S hS hZ X hX hqc hqs hpc
    let tower : ∀ n, Stage B S hS X hX K n :=
      fun n => Nat.rec s₀ (fun n s => (step n s).choose) n
    let map : ∀ n, (tower n).obj ⟶ (tower (n + 1)).obj := fun n =>
      (step n (tower n)).choose_spec.choose
    have hmap : ∀ n, map n ≫ (tower (n + 1)).toTarget = (tower n).toTarget := fun n =>
      (step n (tower n)).choose_spec.choose_spec
    let F : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X hX) := Functor.ofSequence map
    let c : ∀ n, F.obj n ⟶ K := fun n => (tower n).toTarget
    have hc : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) = c n := fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ]
      exact hmap n
    refine ⟨F, c, fun n => (tower n).perfect, fun n => ?_, ?_⟩
    · exact (Stacks.DerivedTruncation.isIso_truncGE_map_iff_forall_isIso_homologyMap (c n)
        _).2 (tower n).isIso
    · exact isHomotopyColimitWith_of_eventually_isIso_homology_modules B S hS X hX
        F c hc fun i => ⟨i.natAbs, fun n hn => (tower n).isIso i (by omega)⟩
  · rintro ⟨F, c, hperf, htrunc, -⟩
    refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ K).2 fun m => ?_
    have hiso : ∀ j : ℤ, -((m.natAbs : ℤ) + 1) ≤ j →
        IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).map
          (c m.natAbs)) :=
      (Stacks.DerivedTruncation.isIso_truncGE_map_iff_forall_isIso_homologyMap (c m.natAbs)
        _).1 (htrunc m.natAbs)
    obtain ⟨C, v, w', hT⟩ := distinguished_cocone_triangle (c m.natAbs)
    have hC : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom C m :=
      RingedSite.isPseudoCoherentFrom_of_forall_isZero_homology _ C m fun i hi =>
        CategoryTheory.isZero_homology_obj₃_of_distinguished (-((m.natAbs : ℤ) + 1)) _ hT
          (fun j hj => hiso j hj.le) (hiso _ le_rfl).epi_of_iso i (by omega)
    exact RingedSite.isPseudoCoherentFrom_of_distinguished_two_general _ m _ hT
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1
        (RingedSite.isPseudoCoherent_of_isPerfect_general _ (hperf m.natAbs)) m) hC

end AlgebraicGeometry.Space

end
