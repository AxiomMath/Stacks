module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.MayerVietorisCover

/-!
# The Čech complex and the alternating Čech complex of an affine open covering

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S = Spec(A)` affine and `X` separated
over `S₀ = Spec(A/I)`, and let `F` be a crystal in quasi-coherent `𝒪_{X/S}`-modules on the small
crystalline site `Cris(X/S)`.  [Stacks, Tag 07MM] chooses an affine open covering
`X = ⋃_{λ ∈ Λ} U_λ`, writes `U_λ = Spec(C_λ)` and chooses a polynomial algebra `P_λ` over `A` with
a surjection `P_λ → C_λ`; out of these choices it builds, for every tuple `α = (λ_0, …, λ_n)`, the
Čech intersection `U_α = U_{λ_0} ∩ ⋯ ∩ U_{λ_n} = Spec(C_α)`, the `p`-adically completed divided
power envelope `D_α` of the kernel of `P_{λ_0} ⊗_A ⋯ ⊗_A P_{λ_n} → C_α`, the cosimplicial divided
power ring `D(n) = ∏_{λ_0 … λ_n} D_α` and the cosimplicial module `M(n) = ∏_{λ_0 … λ_n} M_α` over
it, where `M_α` is the module attached to the restriction of `F` to `Cris(U_α/S)` by
[Stacks, Tag 07JH]; and it asserts

`RΓ(Cris(X/S), F) = s(M(•))`,

`s(-)` being the cochain complex of a cosimplicial module.  [Stacks, Tag 07MN] takes the covering
finite and `Λ` totally ordered, forms the double complex
`M^{n, m} = ⨁_{λ_0 < ⋯ < λ_n} M_α ⊗̂_{D_α} Ω^m_{D_α}` with the alternating Čech differential in the
first and the connection in the second variable, and asserts
`RΓ(Cris(X/S), F) = Tot(M^{•,•})`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `CechCovering` — the first choice of [Stacks, Tag 07MM]: an affine open covering of `X`.
* `CechCovering.inter` — the Čech intersection `U_{λ_0 … λ_n}` of a tuple of indices.
* `CechSystem` — a Čech system of divided power thickenings: the tower
  `T(α)_0 ⟶ T(α)_1 ⟶ ⋯` of objects of `Cris(X/S)` attached to each tuple together with the
  transition morphisms along the inclusions of Čech intersections.  In the remark this is
  `T(α)_e = Spec(D_α/p^e D_α)`.
* `CechSystem.tupleSections` — **the module `M_{λ_0 … λ_n}`**, as `lim_e Γ(T(α)_e, F)`.
* `CechSystem.restriction` — the restriction map `M_{α ∘ φ} ⟶ M_α` along a simplex map.
* `CechSystem.cechSections` — **the cosimplicial module `M(•)`**, in degree `n` the product of the
  `M_α` over the `(n + 1)`-tuples `α`.
* `CechSystem.cechComplex` — **the Čech complex `s(M(•))`**.
* `ComputesCechCohomology` — **the assertion of [Stacks, Tag 07MM]** for a Čech system: the
  cohomology of `s(M(•))` in degree `j` is `H^j(Cris(X/S), F)`.
* `OrdCechTuple`, `OrdCechTuple.omit` — the strictly increasing tuples of [Stacks, Tag 07MN] and
  their faces.
* `OrdDeRhamSystem` — the local completed de Rham complexes `M_β ⊗̂ Ω^*` and the Čech face maps
  between them, with the degree-zero identification of the complex with `M_β`.
* `ordCechTerm` — **the term `M^{n, m}` of the double complex of [Stacks, Tag 07MN]**.
* `ordCechModule` — the alternating Čech module `⨁_{λ_0 < ⋯ < λ_n} M_{λ_0 … λ_n}`, the `m = 0` row
  of that double complex.
* `OrdCechTotalComparison` — **the double complex `M^{•,•}` of [Stacks, Tag 07MN] with its
  prescribed terms and both differentials, and the comparison it asserts**.
* `ComputesOrdCechCohomology` — **the assertion of [Stacks, Tag 07MN]**.

## Main results

* `CechCovering.isSeparated_source` — a scheme separated over the closed fibre of an affine
  divided power base is separated.
* `CechCovering.isAffineOpen_inter` — **every Čech intersection of the chosen covering is affine**
  when `X` is separated.
* `CechCovering.exists_finite_affine_cover` — the chosen covering of a quasi-compact `X` has a
  finite subcovering.
* `CechCovering.iSup_ambientOpen`, `CechCovering.isZariskiCovering_restrictOpenCover` and
  `CechCovering.restrictOpenCover_mem_smallTopology` — **the covering of `X` induces a covering of
  every object of `Cris(X/S)`**.
* `CechSystem.restriction_id` and `CechSystem.restriction_comp` — the restriction maps are
  functorial.
* `CechSystem.cechSections_obj` and `CechSystem.cechComplex_X` — `M(n)` is the product of the `M_α`
  and it is the degree-`n` term of the Čech complex.
* `computesCechCohomology_of_cosimplicialSectionsIso` — **the reduction of [Stacks, Tag 07MM] to
  [Stacks, Tag 07JN]**: once the Čech cosimplicial module `M(•)` of a Čech system is identified
  with the cosimplicial module of a cosimplicial system of thickenings for which the conclusion of
  [Stacks, Tag 07JN] holds, the Čech complex computes `RΓ(Cris(X/S), F)`.
* `computesCechCohomology_zero_iso` — in degree zero the assertion of [Stacks, Tag 07MM] is that
  `H^0(s(M(•)))` is `Γ(Cris(X/S), F)`.
* `ordCechTermZeroIso` — **the `m = 0` row of the double complex of [Stacks, Tag 07MN] is the
  alternating Čech module of the modules `M_β` of [Stacks, Tag 07MM]**.
* `homology_cechComplex_iso_total` — if both remarks hold for the same coefficient sheaf then the
  Čech complex of [Stacks, Tag 07MM] and the total complex of [Stacks, Tag 07MN] have the same
  cohomology, both being `H^*(Cris(X/S), F)`.

## References

* [Stacks Project, Tag 07MM](https://stacks.math.columbia.edu/tag/07MM)
* [Stacks Project, Tag 07MN](https://stacks.math.columbia.edu/tag/07MN)
* [Stacks Project, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 019H](https://stacks.math.columbia.edu/tag/019H)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {Λ : Type u}

/-! ### The chosen affine open covering and its Čech intersections -/

/-- **The first of the two choices of [Stacks, Tag 07MM]**: an affine open covering
`X = ⋃_{λ ∈ Λ} U_λ` of the scheme `X` of a global crystalline situation. -/
structure CechCovering (S : GlobalCrystallineSituation.{u}) (Λ : Type u) where
  /-- The open `U_λ` attached to an index. -/
  opens : Λ → S.X.Opens
  /-- Each member of the covering is affine. -/
  isAffineOpen_opens : ∀ l, IsAffineOpen (opens l)
  /-- The members cover `X`. -/
  iSup_opens : (⨆ l, opens l) = ⊤

namespace CechCovering

variable (c : CechCovering S Λ)

/-- **The Čech intersection `U_{λ_0 … λ_n} = U_{λ_0} ∩ ⋯ ∩ U_{λ_n}`** of [Stacks, Tag 07MM],
attached to a tuple `α = (λ_0, …, λ_n)` of indices. -/
def inter {n : ℕ} (α : Fin (n + 1) → Λ) : S.X.Opens := ⨅ j, c.opens (α j)

/-- A one-element tuple has the corresponding member of the covering as its intersection. -/
@[simp]
theorem inter_const (l : Λ) : c.inter (fun _ : Fin 1 => l) = c.opens l := iInf_const

/-- The Čech intersection of a tuple is contained in each of the members of the covering it
intersects. -/
theorem inter_le {n : ℕ} (α : Fin (n + 1) → Λ) (j : Fin (n + 1)) :
    c.inter α ≤ c.opens (α j) := iInf_le _ j

/-- **If `S` is affine and `X` is separated over `S₀ = Spec(A/I)`, then `X` is separated.** -/
theorem isSeparated_source [IsAffine S.S.scheme]
    [AlgebraicGeometry.IsSeparated S.toClosedFiber] : Scheme.IsSeparated S.X := by
  have : IsAffine (DividedPowerScheme.closedFiber S.S) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine
      (DividedPowerScheme.closedFiberι S.S)).1
  constructor
  rw [← terminal.comp_from S.toClosedFiber]
  infer_instance

/-- **Every Čech intersection of the chosen covering is affine** when `X` is separated. -/
theorem isAffineOpen_inter [Scheme.IsSeparated S.X] {n : ℕ} (α : Fin (n + 1) → Λ) :
    IsAffineOpen (c.inter α) :=
  IsAffineOpen.iInf fun j => c.isAffineOpen_opens (α j)

/-- **The chosen affine open covering of a quasi-compact `X` has a finite subcovering.** -/
theorem exists_finite_affine_cover [CompactSpace S.X] :
    ∃ s : Finset Λ, (⨆ l ∈ s, c.opens l) = ⊤ := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun l : Λ => (c.opens l : Set S.X))
    (fun l => (c.opens l).isOpen) (by
      intro x _
      have hx : x ∈ (⊤ : S.X.Opens) := trivial
      rw [← c.iSup_opens] at hx
      simpa using hx)
  refine ⟨s, top_le_iff.mp ?_⟩
  intro x _
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, by simpa using ⟨hi, hx⟩⟩

/-! ### The covering induced on the small crystalline site -/

/-- **The opens of the ambient scheme of an object of `Cris(X/S)` cut out by the members of the
covering cover that ambient scheme.** -/
theorem iSup_ambientOpen (A : CrystallineThickening S) :
    (⨆ l, CrystallineThickening.ambientOpen A (c.opens l)) = ⊤ := by
  have h : ∀ l, CrystallineThickening.ambientOpen A (c.opens l) =
      Stacks.Thickenings.IsThickening.opensCongr A.obj.thickening.isThickening
        (A.obj.toX ⁻¹ᵁ c.opens l) := fun _ => rfl
  simp only [h]
  rw [← OrderIso.map_iSup]
  rw [A.obj.toX.iSup_preimage_eq_top c.iSup_opens]
  exact OrderIso.map_top _

/-- **The chosen affine open covering of `X` induces a Zariski covering of every object of
`Cris(X/S)`**: the restrictions of an object to the opens its ambient scheme inherits from the
covering form a Zariski covering family. -/
theorem isZariskiCovering_restrictOpenCover (A : CrystallineThickening S) :
    CrystallineThickening.IsZariskiCovering (A.restrictOpenCover
      (fun l : ULift.{u + 1} Λ => CrystallineThickening.ambientOpen A (c.opens l.down))) :=
  CrystallineThickening.isZariskiCovering_restrictOpenCover A
    (fun l : ULift.{u + 1} Λ => CrystallineThickening.ambientOpen A (c.opens l.down))
    fun x => by
      have hx : x ∈ (⨆ l, CrystallineThickening.ambientOpen A (c.opens l)) := by
        rw [c.iSup_ambientOpen A]; trivial
      obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨⟨l⟩, hl⟩

/-- **The covering induced on `Cris(X/S)` by the chosen affine open covering of `X` is a covering
for the Zariski topology of the small crystalline site.** -/
theorem restrictOpenCover_mem_smallTopology (A : CrystallineThickening S) :
    Sieve.generate (A.restrictOpenCover
        (fun l : ULift.{u + 1} Λ =>
          CrystallineThickening.ambientOpen A (c.opens l.down))).presieve₀ ∈
      smallTopology S A :=
  smallZariskiCovering_mem_smallTopology S _ (c.isZariskiCovering_restrictOpenCover A)

end CechCovering

/-! ### Two general facts about limits of sections -/

section Limits

variable {J D E : Type*} [Category J] [Category D] [Category E]

/-- **The map on limits of sections induced by an identity is an identity.** -/
theorem limMap_whiskerRight_op_id (G : J ⥤ D) (F : Dᵒᵖ ⥤ E) [HasLimit (G.op ⋙ F)] :
    limMap (Functor.whiskerRight (NatTrans.op (𝟙 G)) F) = 𝟙 (limit (G.op ⋙ F)) := by
  refine limit.hom_ext fun e => ?_
  simp only [NatTrans.op_id, Functor.whiskerRight_id']
  rw [limMap_π]
  simp

/-- **The maps on limits of sections induced by a composite compose**, contravariantly. -/
theorem limMap_whiskerRight_op_comp {G H K : J ⥤ D} (f : G ⟶ H) (g : H ⟶ K) (F : Dᵒᵖ ⥤ E)
    [HasLimit (G.op ⋙ F)] [HasLimit (H.op ⋙ F)] [HasLimit (K.op ⋙ F)] :
    limMap (Functor.whiskerRight (NatTrans.op (f ≫ g)) F) =
      limMap (Functor.whiskerRight (NatTrans.op g) F) ≫
        limMap (Functor.whiskerRight (NatTrans.op f) F) := by
  refine limit.hom_ext fun e => ?_
  simp only [NatTrans.op_comp, Functor.whiskerRight_comp]
  rw [limMap_π, Category.assoc, limMap_π, limMap_π_assoc]
  simp

end Limits

/-! ### The Čech system of thickenings -/

/-- **A Čech system of divided power thickenings**: for every tuple `α = (λ_0, …, λ_n)` of indices
a tower `T(α)_0 ⟶ T(α)_1 ⟶ T(α)_2 ⟶ ⋯` of objects of `Cris(X/S)`, together with the transition
morphisms along the inclusions `U_α ⊆ U_{α ∘ φ}` of the Čech intersections, functorially in the
simplex category.

In [Stacks, Tag 07MM] the tower is `T(α)_e = Spec(D_α/p^e D_α)` for `D_α` the `p`-adically
completed divided power envelope of the kernel of `P_{λ_0} ⊗_A ⋯ ⊗_A P_{λ_n} → C_α`, and the
transition morphisms come from the inclusions of tensor factors. -/
structure CechSystem (S : GlobalCrystallineSituation.{u}) (Λ : Type u) where
  /-- The tower of thickenings attached to a tuple of indices, covariant in the level. -/
  obj : (n : SimplexCategory) → (Fin (n.len + 1) → Λ) → (ℕ ⥤ CrystallineThickening S)
  /-- The transition morphism of towers along a simplex map. -/
  map : ∀ {m n : SimplexCategory} (φ : m ⟶ n) (α : Fin (n.len + 1) → Λ),
    obj n α ⟶ obj m (fun j => α (φ.toOrderHom j))
  /-- The transition morphism along an identity is an identity. -/
  map_id : ∀ (n : SimplexCategory) (α : Fin (n.len + 1) → Λ), map (𝟙 n) α = 𝟙 (obj n α)
  /-- The transition morphisms compose. -/
  map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (α : Fin (n.len + 1) → Λ),
    map (ψ ≫ φ) α = map φ α ≫ map ψ (fun j => α (φ.toOrderHom j))

namespace CechSystem

variable (T : CechSystem S Λ) (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- **The module `M_{λ_0 … λ_n}` of [Stacks, Tag 07MM]**, read as the limit over the level `e` of
the sections of `F` over `T(α)_e`.  For `F` a crystal in quasi-coherent `𝒪_{X/S}`-modules and
`T(α)_e = Spec(D_α/p^e D_α)` this is the `D_α`-module corresponding to the restriction of `F` to
`Cris(U_α/S)` under [Stacks, Tag 07JH]. -/
def tupleSections {n : SimplexCategory} (α : Fin (n.len + 1) → Λ) : AddCommGrpCat.{u + 1} :=
  limit ((T.obj n α).op ⋙ F)

/-- **The restriction map `M_{α ∘ φ} ⟶ M_α`** induced by a simplex map, that is, by the inclusion
`U_α ⊆ U_{α ∘ φ}` of Čech intersections. -/
def restriction {m n : SimplexCategory} (φ : m ⟶ n) (α : Fin (n.len + 1) → Λ) :
    T.tupleSections F (fun j => α (φ.toOrderHom j)) ⟶ T.tupleSections F α :=
  limMap (Functor.whiskerRight (NatTrans.op (T.map φ α)) F)

/-- The restriction map along an identity is an identity. -/
@[simp]
theorem restriction_id (n : SimplexCategory) (α : Fin (n.len + 1) → Λ) :
    T.restriction F (𝟙 n) α = 𝟙 (T.tupleSections F α) := by
  simp only [restriction, T.map_id]
  exact limMap_whiskerRight_op_id _ _

/-- The restriction maps compose, contravariantly in the simplex category. -/
theorem restriction_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (α : Fin (n.len + 1) → Λ) :
    T.restriction F (ψ ≫ φ) α =
      T.restriction F ψ (fun j => α (φ.toOrderHom j)) ≫ T.restriction F φ α := by
  simp only [restriction, T.map_comp]
  exact limMap_whiskerRight_op_comp _ _ _

/-- **The cosimplicial module `M(•)` of [Stacks, Tag 07MM]**: in degree `n` the product

`M(n) = ∏_{λ_0 … λ_n} M_{λ_0 … λ_n}`

over all `(n + 1)`-tuples of indices of the covering, with the cosimplicial structure maps given
componentwise by the restriction maps along the inclusions of the Čech intersections. -/
def cechSections : CosimplicialObject AddCommGrpCat.{u + 1} where
  obj n := ∏ᶜ fun α : Fin (n.len + 1) → Λ => T.tupleSections F α
  map φ := Pi.lift fun α => Pi.π _ (fun j => α (φ.toOrderHom j)) ≫ T.restriction F φ α
  map_id n := by
    refine Pi.hom_ext _ _ fun α => ?_
    simp only [Pi.lift_π, T.restriction_id, Category.id_comp]
    rfl
  map_comp ψ φ := by
    refine Pi.hom_ext _ _ fun α => ?_
    simp only [Pi.lift_π, T.restriction_comp, Category.assoc, Pi.lift_π_assoc]
    rfl

/-- **`M(n)` is the product of the modules `M_{λ_0 … λ_n}` over the `(n + 1)`-tuples of indices of
the covering.** -/
theorem cechSections_obj (n : ℕ) :
    (T.cechSections F).obj ⦋n⦌ = ∏ᶜ fun α : Fin (n + 1) → Λ => T.tupleSections F α := rfl

/-- **The Čech complex `s(M(•))` of [Stacks, Tag 07MM]**: the cochain complex associated to the
cosimplicial module `M(•)`, that is, its alternating coface map complex. -/
def cechComplex : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (T.cechSections F)

/-- **The degree-`n` term of the Čech complex is `M(n)`.** -/
theorem cechComplex_X (n : ℕ) : (T.cechComplex F).X n = (T.cechSections F).obj ⦋n⦌ := rfl

end CechSystem

/-! ### The assertion of [Stacks, Tag 07MM] -/

/-- **The property that the Čech complex of a Čech system computes `RΓ(Cris(X/S), F)`**, in the
graded form in which the cohomology of the small crystalline site is available here: the cohomology
of `s(M(•))` in degree `j` is `H^j(Cris(X/S), F)`, for every `j`.

This is the conclusion asserted by [Stacks, Tag 07MM]. -/
def ComputesCechCohomology (T : CechSystem S Λ)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ j : ℕ, Nonempty ((T.cechComplex F.obj).homology j ≅ (cohomologyFunctor S j).obj F)

/-- In degree zero the conclusion of [Stacks, Tag 07MM] says that the cohomology of the Čech
complex in degree zero is the global sections `Γ(Cris(X/S), F)`. -/
theorem computesCechCohomology_zero_iso (T : CechSystem S Λ)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (h : ComputesCechCohomology T F) :
    Nonempty ((T.cechComplex F.obj).homology 0 ≅ (globalSections S).obj F) :=
  ⟨(h 0).some ≪≫ (cohomologyFunctorZeroIso S).app F⟩

/-- **The reduction of [Stacks, Tag 07MM] to [Stacks, Tag 07JN].**  Suppose the Čech cosimplicial
module `M(•)` of a Čech system `T` is isomorphic, as a cosimplicial module, to the cosimplicial
module `n ↦ lim_e Γ(W(n)_e, F)` of a cosimplicial system `W` of thickenings for which the
conclusion of [Stacks, Tag 07JN] holds — that is, for which
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesCohomology W F`.  Then the Čech complex
`s(M(•))` of `T` computes `RΓ(Cris(X/S), F)`, which is the conclusion of [Stacks, Tag 07MM]. -/
theorem computesCechCohomology_of_cosimplicialSectionsIso {T : CechSystem S Λ}
    {W : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
    {F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (e : T.cechSections F.obj ≅ cosimplicialSections W F.obj)
    (h : ComputesCohomology W F) : ComputesCechCohomology T F := fun j =>
  ⟨(HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) j).mapIso
      ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).mapIso e) ≪≫
    (h j).some⟩

/-! ### The alternating Čech complex of [Stacks, Tag 07MN] -/

section Alternating

variable [LinearOrder Λ]

/-- **A strictly increasing tuple `λ_0 < ⋯ < λ_n` of indices** of the covering, the index of the
alternating Čech complex of [Stacks, Tag 07MN]. -/
abbrev OrdCechTuple (Λ : Type u) [LinearOrder Λ] (n : ℕ) : Type u :=
  {α : Fin (n + 1) → Λ // StrictMono α}

/-- **Omitting the `i`-th index of a strictly increasing tuple**, which is again strictly
increasing.  These are the faces along which the alternating Čech differential is formed. -/
def OrdCechTuple.omit {n : ℕ} (β : OrdCechTuple Λ (n + 1)) (i : Fin (n + 2)) : OrdCechTuple Λ n :=
  ⟨β.1 ∘ i.succAbove, β.2.comp (Fin.strictMono_succAbove i)⟩

/-- **A finite covering has only finitely many strictly increasing tuples of indices.** -/
instance OrdCechTuple.finite [Finite Λ] (n : ℕ) : Finite (OrdCechTuple Λ n) :=
  Subtype.finite

/-- **The local de Rham complexes and Čech faces that [Stacks, Tag 07MN] forms its double complex
from**: for every strictly increasing tuple `β = (λ_0 < ⋯ < λ_n)` a cochain complex, which in the
remark is the `p`-adically completed de Rham complex

`M_{λ_0 … λ_n} ⊗̂_{D_{λ_0 … λ_n}} Ω^*_{D_{λ_0 … λ_n}}`

of the module `M_β` of [Stacks, Tag 07MM] for the integrable connection `∇` of
[Stacks, Tag 07JH]; together with the maps induced by omitting one index, which in degree zero are
the restriction maps of [Stacks, Tag 07MM].

The degree-zero term of each complex is identified with `M_β` by `zeroIso`. -/
structure OrdDeRhamSystem (T : CechSystem S Λ)
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) where
  /-- The local completed de Rham complex at a strictly increasing tuple. -/
  complex : (n : ℕ) → OrdCechTuple Λ n → CochainComplex AddCommGrpCat.{u + 1} ℕ
  /-- Its degree-zero term is the module `M_{λ_0 … λ_n}` of [Stacks, Tag 07MM]. -/
  zeroIso : ∀ (n : ℕ) (β : OrdCechTuple Λ n), (complex n β).X 0 ≅ T.tupleSections F β.1
  /-- The map of local complexes induced by omitting one index of the tuple. -/
  face : ∀ (n : ℕ) (β : OrdCechTuple Λ (n + 1)) (i : Fin (n + 2)),
    complex n (β.omit i) ⟶ complex (n + 1) β
  /-- In degree zero the face map is the restriction map of [Stacks, Tag 07MM] along the
  corresponding inclusion of Čech intersections. -/
  face_zero : ∀ (n : ℕ) (β : OrdCechTuple Λ (n + 1)) (i : Fin (n + 2)),
    (face n β i).f 0 ≫ (zeroIso (n + 1) β).hom =
      (zeroIso n (β.omit i)).hom ≫ T.restriction F (SimplexCategory.δ i) β.1

/-- **The term `M^{n, m}` of the double complex of [Stacks, Tag 07MN]**: the product, over the
strictly increasing `(n + 1)`-tuples of indices of the covering, of the degree-`m` terms of the
local completed de Rham complexes.  The covering of the remark is finite, so this product is the
direct sum `⨁_{λ_0 < ⋯ < λ_n}` of the source. -/
def ordCechTerm {T : CechSystem S Λ} {F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (K : OrdDeRhamSystem T F) (n m : ℕ) : AddCommGrpCat.{u + 1} :=
  ∏ᶜ fun β : OrdCechTuple Λ n => (K.complex n β).X m

/-- **The alternating Čech module `⨁_{λ_0 < ⋯ < λ_n} M_{λ_0 … λ_n}`** of the modules `M_β` of
[Stacks, Tag 07MM], indexed by the strictly increasing tuples of [Stacks, Tag 07MN].  This is the
`m = 0` row of the double complex of that remark, by `ordCechTermZeroIso`. -/
def ordCechModule (T : CechSystem S Λ)
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) : AddCommGrpCat.{u + 1} :=
  ∏ᶜ fun β : OrdCechTuple Λ n => T.tupleSections F β.1

/-- **The `m = 0` row of the double complex of [Stacks, Tag 07MN] is the alternating Čech module of
the modules `M_{λ_0 … λ_n}` of [Stacks, Tag 07MM].** -/
def ordCechTermZeroIso {T : CechSystem S Λ}
    {F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (K : OrdDeRhamSystem T F) (n : ℕ) :
    ordCechTerm K n 0 ≅ ordCechModule T F n :=
  Limits.Pi.mapIso fun β => K.zeroIso n β

/-- **The double complex `M^{•,•}` of [Stacks, Tag 07MN] together with the comparison it asserts.**
The fields say: the double complex is concentrated in the first quadrant; its term in bidegree
`(n, m)` is `M^{n, m}`; its second differential is the differential of the local de Rham complexes,
that is, the connection; its first differential is the usual alternating Čech differential
`∑_i (-1)^i` of the face maps; its total complex exists; and the total complex computes
`RΓ(Cris(X/S), F)`, in the graded form in which the cohomology of the small crystalline site is
available here. -/
structure OrdCechTotalComparison [Finite Λ] {T : CechSystem S Λ}
    {F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (K : OrdDeRhamSystem T F)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) where
  /-- The double complex `M^{•,•}`, with the Čech degree first and the de Rham degree second. -/
  double : HomologicalComplex₂ AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  /-- In every bidegree of the first quadrant the term is `M^{n, m}`. -/
  termIso : ∀ n m : ℕ, (double.X (n : ℤ)).X (m : ℤ) ≅ ordCechTerm K n m
  /-- The double complex vanishes in negative Čech degree. -/
  isZero_of_neg_cech : ∀ n m : ℤ, n < 0 → IsZero ((double.X n).X m)
  /-- The double complex vanishes in negative de Rham degree. -/
  isZero_of_neg_deRham : ∀ n m : ℤ, m < 0 → IsZero ((double.X n).X m)
  /-- The second differential is the differential of the local de Rham complexes. -/
  deRhamDifferential : ∀ (n m : ℕ) (β : OrdCechTuple Λ n),
    (double.X (n : ℤ)).d (m : ℤ) ((m + 1 : ℕ) : ℤ) ≫ (termIso n (m + 1)).hom ≫ Pi.π _ β =
      ((termIso n m).hom ≫ Pi.π _ β) ≫ (K.complex n β).d m (m + 1)
  /-- The first differential is the alternating Čech differential of the face maps. -/
  cechDifferential : ∀ (n m : ℕ) (β : OrdCechTuple Λ (n + 1)),
    (double.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).f (m : ℤ) ≫ (termIso (n + 1) m).hom ≫ Pi.π _ β =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        ((termIso n m).hom ≫ Pi.π _ (β.omit i) ≫ (K.face n β i).f m)
  /-- The total complex exists, the double complex being concentrated in the first quadrant. -/
  hasTotal : double.HasTotal (ComplexShape.up ℤ)
  /-- **The assertion of [Stacks, Tag 07MN]**: the total complex computes
  `RΓ(Cris(X/S), F)`. -/
  computesCohomology :
    letI := hasTotal
    ∀ j : ℕ, Nonempty ((double.total (ComplexShape.up ℤ)).homology (j : ℤ) ≅
      (cohomologyFunctor S j).obj G)

/-- **The assertion of [Stacks, Tag 07MN]**: the alternating Čech double complex of the local
completed de Rham complexes exists and its total complex computes `RΓ(Cris(X/S), F)`. -/
def ComputesOrdCechCohomology [Finite Λ] {T : CechSystem S Λ}
    {F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (K : OrdDeRhamSystem T F)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  Nonempty (OrdCechTotalComparison K G)

/-- **If both [Stacks, Tag 07MM] and [Stacks, Tag 07MN] hold for the same coefficient sheaf then
the Čech complex of the first and the total complex of the alternating Čech double complex of the
second have the same cohomology**, both of them being `H^*(Cris(X/S), F)`. -/
theorem homology_cechComplex_iso_total [Finite Λ] {T : CechSystem S Λ}
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} {K : OrdDeRhamSystem T G.obj}
    (hM : ComputesCechCohomology T G) (hN : OrdCechTotalComparison K G) (j : ℕ) :
    letI := hN.hasTotal
    Nonempty ((T.cechComplex G.obj).homology j ≅
      (hN.double.total (ComplexShape.up ℤ)).homology (j : ℤ)) :=
  ⟨(hM j).some ≪≫ (hN.computesCohomology j).some.symm⟩

end Alternating

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
