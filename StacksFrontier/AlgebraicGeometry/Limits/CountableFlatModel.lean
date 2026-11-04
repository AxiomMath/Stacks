module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystemModels
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeSystemMorphism
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.GoodDiagramExistence
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import Mathlib.Data.Finsupp.Encodable

/-!
# A flat morphism of finite presentation over a ring is a base change from countable rings

Let `A` be a ring, `X` a scheme of finite presentation over `A` and `f : U ⟶ X` a flat morphism
of finite presentation. Then `f` is the base change, along some `g : X ⟶ X₀`, of a flat,
quasi-compact and quasi-separated morphism `f₀ : U₀ ⟶ X₀` between quasi-compact and
quasi-separated schemes whose rings of sections over affine opens are all countable.

## Main results

* `AlgebraicGeometry.countable_of_finiteType`: a finitely generated algebra over a countable ring
  is countable.
* `AlgebraicGeometry.countable_sections_of_locallyOfFiniteType`: a scheme locally of finite type
  over an affine scheme with countable ring of global sections has countable rings of sections
  over its affine opens.
* `AlgebraicGeometry.exists_countable_flat_model`: the model `f₀` above.

## References

* [Stacks Project, Tag 0CRR](https://stacks.math.columbia.edu/tag/0CRR)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
* [Stacks Project, Tag 0CNT](https://stacks.math.columbia.edu/tag/0CNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A finitely generated algebra over a countable ring is countable.** -/
theorem countable_of_finiteType (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [Countable R] [Algebra.FiniteType R B] : Countable B := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹_›
  have : Countable (AddMonoidAlgebra R (Fin n →₀ ℕ)) :=
    Function.Injective.countable (f := AddMonoidAlgebra.coeff)
      (fun a b h => by cases a; cases b; cases h; rfl)
  have : Countable (MvPolynomial (Fin n) R) := this
  exact hf.countable

/-- **Countable rings of sections over affine opens, from finite type over a countable affine
base.** If `q : Y ⟶ S` is locally of finite type and `S` is affine with countable ring of global
sections, then the ring of sections of `Y` over every affine open is countable. -/
theorem countable_sections_of_locallyOfFiniteType {Y S : Scheme.{u}} (q : Y ⟶ S)
    [LocallyOfFiniteType q] [IsAffine S] (hS : Countable Γ(S, ⊤)) (V : Y.Opens)
    (hV : IsAffineOpen V) : Countable Γ(Y, V) := by
  have e : V ≤ q ⁻¹ᵁ ⊤ := by rw [Scheme.Hom.preimage_top]; exact le_top
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType q inferInstance ⟨⊤, isAffineOpen_top S⟩
    ⟨V, hV⟩ e
  let := (q.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.FiniteType Γ(S, ⊤) Γ(Y, V) := h
  exact countable_of_finiteType Γ(S, ⊤) Γ(Y, V)

/-- The stages of the Noetherian approximation of `Spec A` by the spectra of its finitely
generated subrings have countable rings of global sections. -/
theorem countable_sections_top_specAdjoinFinsetDiagram_obj (A : Type u) [CommRing A]
    (i : (Finset A)ᵒᵖ) : Countable Γ((specAdjoinFinsetDiagram A).obj i, ⊤) := by
  have := finiteType_adjoinFinset_int A i.unop
  have : Countable (Algebra.adjoin ℤ ((i.unop : Finset A) : Set A)) :=
    countable_of_finiteType ℤ _
  exact Function.Injective.countable (f := (Scheme.ΓSpecIso (CommRingCat.of
    (Algebra.adjoin ℤ ((i.unop : Finset A) : Set A)))).hom.hom)
    ((ConcreteCategory.bijective_of_isIso _).1)

section Stage

variable {A : Type u} [CommRing A] {Y : Scheme.{u}}
  {q : Y ⟶ (specLimitNoetherianSituation A).limitScheme}

/-- The stages of the system of scheme-theoretic images of a good diagram over the Noetherian
approximation of `Spec A` are of finite type over a stage of the base system. -/
theorem locallyOfFiniteType_imageSystem_obj
    (G : LimitNoetherianSituation.GoodDiagram (specLimitNoetherianSituation A) q)
    (k : Over (op G.index)) :
    LocallyOfFiniteType ((G.stageMap k).imageι ≫ pullback.fst _ _) := by
  have := G.locallyOfFiniteType
  infer_instance

/-- The stages of the system of scheme-theoretic images of a good diagram over the Noetherian
approximation of `Spec A` are quasi-compact, quasi-separated, and have countable rings of
sections over affine opens. -/
theorem compactSpace_quasiSeparatedSpace_countable_imageSystem_obj
    (G : LimitNoetherianSituation.GoodDiagram (specLimitNoetherianSituation A) q)
    (k : Over (op G.index)) :
    CompactSpace ((LimitNoetherianSituation.GoodDiagram.imageSystem G).obj k) ∧
      QuasiSeparatedSpace ((LimitNoetherianSituation.GoodDiagram.imageSystem G).obj k) ∧
      ∀ V : ((LimitNoetherianSituation.GoodDiagram.imageSystem G).obj k).Opens,
        IsAffineOpen V →
          Countable Γ((LimitNoetherianSituation.GoodDiagram.imageSystem G).obj k, V) := by
  have := G.locallyOfFiniteType
  have := G.quasiCompact
  have hS := (specLimitNoetherianSituation A).noetherian k.left.unop
  let r := (G.stageMap k).imageι ≫ pullback.fst _ _
  have : LocallyOfFiniteType r := locallyOfFiniteType_imageSystem_obj G k
  have : QuasiCompact r := inferInstance
  have hc : CompactSpace ((LimitNoetherianSituation.GoodDiagram.imageSystem G).obj k) :=
    QuasiCompact.compactSpace_of_compactSpace r
  have : IsLocallyNoetherian ((LimitNoetherianSituation.GoodDiagram.imageSystem G).obj k) :=
    LocallyOfFiniteType.isLocallyNoetherian r
  have : IsNoetherian ((LimitNoetherianSituation.GoodDiagram.imageSystem G).obj k) := ⟨⟩
  refine ⟨hc, inferInstance, fun V hV => ?_⟩
  have : IsAffine ((specLimitNoetherianSituation A).system.obj k.left) :=
    isAffine_specAdjoinFinsetDiagram_obj A k.left
  exact countable_sections_of_locallyOfFiniteType r
    (countable_sections_top_specAdjoinFinsetDiagram_obj A k.left) V hV

end Stage

/-- **A flat morphism of finite presentation over a ring is a base change of a flat morphism
between schemes with countable rings of sections.** Let `X` be of finite presentation over a
ring `A` and `f : U ⟶ X` flat and of finite presentation. Then there are a flat, quasi-compact
and quasi-separated `f₀ : U₀ ⟶ X₀`, with `U₀` and `X₀` quasi-compact, quasi-separated and with
countable rings of sections over affine opens, and a cartesian square
`U ⟶ U₀`, `f`, `f₀`, `X ⟶ X₀`. -/
theorem exists_countable_flat_model {A : Type u} [CommRing A] {X U : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (f : U ⟶ X) [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (X₀ U₀ : Scheme.{u}) (g : X ⟶ X₀) (g' : U ⟶ U₀) (f₀ : U₀ ⟶ X₀),
      IsPullback g' f f₀ g ∧ Flat f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
      CompactSpace X₀ ∧ QuasiSeparatedSpace X₀ ∧ CompactSpace U₀ ∧ QuasiSeparatedSpace U₀ ∧
      (∀ V : X₀.Opens, IsAffineOpen V → Countable Γ(X₀, V)) ∧
      (∀ V : U₀.Opens, IsAffineOpen V → Countable Γ(U₀, V)) := by
  let D := specLimitNoetherianSituation A
  let p' : X ⟶ D.limitScheme := p
  have : QuasiSeparated p' := ‹QuasiSeparated p›
  have : QuasiCompact p' := ‹QuasiCompact p›
  have : LocallyOfFinitePresentation p' := ‹LocallyOfFinitePresentation p›
  obtain ⟨GX⟩ := LimitNoetherianSituation.nonempty_goodDiagram D p'
  obtain ⟨GU⟩ := LimitNoetherianSituation.nonempty_goodDiagram D (f ≫ p')
  obtain ⟨i₀, hU, hX, ⟨F⟩⟩ := LimitNoetherianSituation.exists_morphismAt D f rfl GU GX
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨i₁, hi₁, hflat⟩ :=
    LimitNoetherianSituation.eventually_flat_morphismAt' D f rfl hfp GU GX i₀ hU hX F
  obtain ⟨i₂, hi₂, hpb⟩ :=
    LimitNoetherianSituation.eventually_isPullback_limit_morphismAt' D f rfl hfp GU GX i₀ hU hX F
  classical
  obtain ⟨i₃, h₁, h₂⟩ : ∃ i₃ : Finset A, i₁ ≤ i₃ ∧ i₂ ≤ i₃ :=
    ⟨i₁ ∪ i₂, Finset.subset_union_left, Finset.subset_union_right⟩
  let j : Over (op i₀) := Over.mk (homOfLE (hi₁.trans h₁)).op
  let kX := (Over.map ((homOfLE hX).op)).obj j
  let kU := (Over.map ((homOfLE hU).op)).obj j
  obtain ⟨hXc, hXs, hXct⟩ := compactSpace_quasiSeparatedSpace_countable_imageSystem_obj GX kX
  obtain ⟨hUc, hUs, hUct⟩ := compactSpace_quasiSeparatedSpace_countable_imageSystem_obj GU kU
  let f₀ := F.maps.app j
  have hf₀ : Flat f₀ := hflat j h₁
  have hterm : f₀ ≫ terminal.from _ = terminal.from _ := terminal.hom_ext _ _
  have hqs : QuasiSeparated f₀ := by
    have : QuasiSeparated (f₀ ≫ terminal.from _) := by
      rw [hterm]
      exact (quasiSeparatedSpace_iff_quasiSeparated _).1 hUs
    exact QuasiSeparated.of_comp f₀ (terminal.from _)
  have hqc : QuasiCompact f₀ := by
    have : QuasiSeparated (terminal.from ((Over.map (homOfLE hX).op ⋙
        LimitNoetherianSituation.GoodDiagram.imageSystem GX).obj j)) :=
      (quasiSeparatedSpace_iff_quasiSeparated _).1 hXs
    have : QuasiCompact (f₀ ≫ terminal.from _) := by
      rw [hterm]
      exact (quasiCompact_iff_compactSpace _).2 hUc
    exact QuasiCompact.of_comp f₀ (terminal.from _)
  exact ⟨_, _, (LimitNoetherianSituation.GoodDiagram.imageCone GX).π.app kX,
    (LimitNoetherianSituation.GoodDiagram.imageCone GU).π.app kU, f₀, (hpb j h₂).flip, hf₀,
    hqc, hqs, hXc, hXs, hUc, hUs, hXct, hUct⟩

end AlgebraicGeometry

end
