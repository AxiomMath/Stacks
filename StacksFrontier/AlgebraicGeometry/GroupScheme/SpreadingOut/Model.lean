module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.SpreadingOut.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.RelationModel
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Spreading out a commutative group scheme

Let `S = lim Sᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition morphisms, and let `A` be a commutative group scheme over `S`, separated and of finite
presentation. Then `A` is the base change, as a group scheme, of a commutative group scheme over
some stage `Sᵢ`, separated and of finite presentation over it.

Applied to the presentation of `Spec k` as the limit of the spectra of the finitely generated
subrings of `k`, this spreads a commutative group scheme over a field `k` out to a commutative
group scheme over a finitely generated `ℤ`-subalgebra of `k`.

## Main results

* `AlgebraicGeometry.exists_grpObj_model_of_isLimit`: the model over a stage of a cofiltered
  limit.
* `AlgebraicGeometry.exists_grpObj_model_of_isLimit_of_hom`: the same, below a given stage.
* `AlgebraicGeometry.exists_grpObj_model`: the model over a finitely generated subring of a field.
* `AlgebraicGeometry.exists_grpObj_model_of_finset`: the same, over a subring containing given
  elements.

## Implementation notes

The scheme `A` is first descended to a separated scheme `X` of finite presentation over a stage,
with an identification `e` of its base change with `A`. The multiplication, the unit and the
inverse of `A` are then descended one at a time, each by
`AlgebraicGeometry.RelationModel.exists_hom_model`, to morphisms of `X` over later stages which
are models of them in the sense of `CategoryTheory.IsMulModel`, `CategoryTheory.IsOneModel` and
`CategoryTheory.IsInvModel`; passing to a later stage preserves these model conditions because
the comparison `AlgebraicGeometry.overPullbackCompNatIso` between iterated and direct base change
is a natural isomorphism of monoidal functors into a cartesian monoidal category. The group
axioms and commutativity of the models hold after base change to the limit, hence after base
change to a later stage by `AlgebraicGeometry.RelationModel.eventuallyBelow_map_eq`, where
`CategoryTheory.grpObjOfMap` assembles the group scheme.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZQ](https://stacks.math.columbia.edu/tag/01ZQ)
* [Stacks Project, Tag 022T](https://stacks.math.columbia.edu/tag/022T)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry

/-! ### Base change and the cartesian monoidal structure -/

/-- The comparison `AlgebraicGeometry.overPullbackCompIso` between iterated and direct base
change, as a natural isomorphism of functors. -/
def overPullbackCompNatIso {S S' T : Scheme.{u}} (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T)
    (h : q ≫ p = r) : Over.pullback p ⋙ Over.pullback q ≅ Over.pullback r :=
  NatIso.ofComponents (overPullbackCompIso p q r h)
    (fun f => (overPullbackCompIso_naturality p q r h f).symm)

/-- The binary product of two schemes of finite presentation over `S`, in the cartesian monoidal
structure of `Over S`, is of finite presentation over `S`. -/
lemma finitePresentation_tensorObj_hom {S : Scheme.{u}} {X Y : Over S}
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) :
    FinitePresentation (X ⊗ Y).hom := by
  have h₁ : FinitePresentation (pullback.fst X.hom Y.hom) :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback X.hom Y.hom).flip hY
  have h₂ := FinitePresentation.comp h₁ hX
  have := h₂.1; have := h₂.2.1; have := h₂.2.2
  exact ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (QuasiCompact (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (QuasiSeparated (pullback.fst X.hom Y.hom ≫ X.hom))⟩

/-- The unit of the cartesian monoidal structure of `Over S` is of finite presentation over
`S`. -/
lemma finitePresentation_tensorUnit_hom (S : Scheme.{u}) :
    FinitePresentation (𝟙_ (Over S)).hom :=
  ⟨inferInstanceAs (LocallyOfFinitePresentation (𝟙 S)),
    inferInstanceAs (QuasiCompact (𝟙 S)), inferInstanceAs (QuasiSeparated (𝟙 S))⟩

/-! ### Models of a group scheme over a stage -/

section Model

open MonObj

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

variable (c) in
/-- A model over a stage of a scheme `A` over the limit: a separated scheme of finite
presentation over the stage together with an identification of its base change with `A`. -/
structure SchemeModel (A : Over c.pt) where
  /-- The stage the model is defined over. -/
  stage : I
  /-- The model of `A`. -/
  X : Over (D.obj stage)
  /-- The model is of finite presentation over the stage. -/
  finitePresentation : FinitePresentation X.hom
  /-- The model is separated over the stage. -/
  isSeparated : IsSeparated X.hom
  /-- The identification of the base change of the model with `A`. -/
  e : (Over.pullback (c.π.app stage)).obj X ≅ A

namespace SchemeModel

variable {A : Over c.pt} (M : SchemeModel c A)

/-- The comparison between base change to a later stage followed by base change to the limit,
and base change to the limit. -/
abbrev τ {k : I} (a : k ⟶ M.stage) :
    Over.pullback (D.map a) ⋙ Over.pullback (c.π.app k) ≅ Over.pullback (c.π.app M.stage) :=
  overPullbackCompNatIso (D.map a) (c.π.app k) (c.π.app M.stage) (c.w a)

/-- The model over a later stage obtained by base change along a transition morphism. -/
abbrev restrict {k : I} (a : k ⟶ M.stage) : SchemeModel c A where
  stage := k
  X := (Over.pullback (D.map a)).obj M.X
  finitePresentation := finitePresentation_overPullbackObj _ _ M.finitePresentation
  isSeparated := MorphismProperty.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback M.X.hom (D.map a)) M.isSeparated
  e := (M.τ a).app M.X ≪≫ M.e

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- The identification of a restriction of a model. -/
lemma restrict_e {k : I} (a : k ⟶ M.stage) : (M.restrict a).e = (M.τ a).app M.X ≪≫ M.e := rfl

/-- Base change from the stage of the model to the limit. -/
abbrev F : Over (D.obj M.stage) ⥤ Over c.pt := Over.pullback (c.π.app M.stage)

/-- A morphism over the limit between the base changes of two schemes of finite presentation over
the stage of a model descends to a later stage. -/
lemma exists_hom (hc : IsLimit c) {X Y : Over (D.obj M.stage)} (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom) {X' Y' : Over c.pt} (eX : M.F.obj X ≅ X') (eY : M.F.obj Y ≅ Y')
    (f : X' ⟶ Y') :
    ∃ (k : I) (a : k ⟶ M.stage)
      (g : (Over.pullback (D.map a)).obj X ⟶ (Over.pullback (D.map a)).obj Y),
      (Over.pullback (c.π.app k)).map g ≫ (M.τ a).hom.app Y ≫ eY.hom =
        (M.τ a).hom.app X ≫ eX.hom ≫ f :=
  RelationModel.exists_hom_model hc X Y hX hY eX eY f

variable [GrpObj A]

/-- The multiplication of `A` descends to a model over a later stage. -/
lemma exists_isMulModel (hc : IsLimit c) :
    ∃ (k : I) (a : k ⟶ M.stage) (m : (M.restrict a).X ⊗ (M.restrict a).X ⟶ (M.restrict a).X),
      IsMulModel (Over.pullback (c.π.app k)) (M.restrict a).e m := by
  obtain ⟨k, a, g, hg⟩ := M.exists_hom hc
    (finitePresentation_tensorObj_hom M.finitePresentation M.finitePresentation)
    M.finitePresentation ((Functor.Monoidal.μIso M.F M.X M.X).symm ≪≫ tensorIso M.e M.e) M.e
    μ[A]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv, tensorIso_hom,
    Category.assoc] at hg
  exact ⟨k, a, _, isMulModel_of_map (M.τ a) hg⟩

/-- The unit of `A` descends to a model over a later stage. -/
lemma exists_isOneModel (hc : IsLimit c) :
    ∃ (k : I) (a : k ⟶ M.stage) (u : 𝟙_ _ ⟶ (M.restrict a).X),
      IsOneModel (Over.pullback (c.π.app k)) (M.restrict a).e u := by
  obtain ⟨k, a, g, hg⟩ := M.exists_hom hc (finitePresentation_tensorUnit_hom _)
    M.finitePresentation (Functor.Monoidal.εIso M.F).symm M.e η[A]
  exact ⟨k, a, _, isOneModel_of_map (M.τ a) hg⟩

/-- The inverse of `A` descends to a model over a later stage. -/
lemma exists_isInvModel (hc : IsLimit c) :
    ∃ (k : I) (a : k ⟶ M.stage) (i : (M.restrict a).X ⟶ (M.restrict a).X),
      IsInvModel (Over.pullback (c.π.app k)) (M.restrict a).e i := by
  obtain ⟨k, a, g, hg⟩ := M.exists_hom hc M.finitePresentation M.finitePresentation M.e M.e ι[A]
  exact ⟨k, a, g, isInvModel_of_map (M.τ a) (by rw [Category.assoc]; exact hg)⟩

end SchemeModel

/-- A separated scheme of finite presentation over the limit has a model over a stage. -/
lemma SchemeModel.nonempty (hc : IsLimit c) (A : Over c.pt) (hA : FinitePresentation A.hom)
    [IsSeparated A.hom] : Nonempty (SchemeModel c A) := by
  obtain ⟨j₀, X₀, hX₀, ⟨e₀⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc A hA
  have : QuasiCompact X₀.hom := hX₀.2.1
  have : QuasiSeparated X₀.hom := hX₀.2.2
  have : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  have : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  have : IsSeparated ((Over.pullback (c.π.app j₀)).obj X₀).hom :=
    prop_of_overIso (@IsSeparated) e₀ ‹_›
  obtain ⟨j, a, hsep⟩ := exists_isSeparated_overPullback_of_isLimit D c hc j₀ X₀
  exact ⟨{ stage := j
           X := (Over.pullback (D.map a)).obj X₀
           finitePresentation := finitePresentation_overPullbackObj _ _ hX₀
           isSeparated := hsep
           e := overPullbackCompIso (D.map a) (c.π.app j) (c.π.app j₀) (c.w a) X₀ ≪≫ e₀.symm }⟩

/-- **Spreading out a commutative group scheme over a cofiltered limit, below a given stage.** Let
`S = lim Sᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, let `A` be a commutative group scheme over `S`, separated and of finite presentation,
and let `j₀` be a stage. Then there are a stage `Sₖ` with a transition morphism `k ⟶ j₀`, a
commutative group scheme `𝒜` over `Sₖ`, separated and of finite presentation, and an isomorphism
of group schemes from the base change of `𝒜` to `A`. -/
theorem exists_grpObj_model_of_isLimit_of_hom (hc : IsLimit c) (A : Over c.pt) [GrpObj A]
    [IsCommMonObj A] (hA : FinitePresentation A.hom) [IsSeparated A.hom] (j₀ : I) :
    ∃ (k : I) (_ : k ⟶ j₀) (𝒜 : Grp (Over (D.obj k))) (_ : IsCommMonObj 𝒜.X)
      (e : ((Over.pullback (c.π.app k)).mapGrp.obj 𝒜).X ≅ A),
      FinitePresentation 𝒜.X.hom ∧ IsSeparated 𝒜.X.hom ∧ IsMonHom e.hom := by
  obtain ⟨Mᵢ⟩ := SchemeModel.nonempty hc A hA
  let M₀ := Mᵢ.restrict (IsCofiltered.minToLeft Mᵢ.stage j₀)
  -- the multiplication
  obtain ⟨k₁, a₁, m₁, hm₁⟩ := M₀.exists_isMulModel hc
  let M₁ := M₀.restrict a₁
  -- the unit
  obtain ⟨k₂, a₂, u₂, hu₂⟩ := M₁.exists_isOneModel hc
  let M₂ := M₁.restrict a₂
  have hm₂ := hm₁.comp (M₁.τ a₂)
  -- the inverse
  obtain ⟨k₃, a₃, i₃, hi₃⟩ := M₂.exists_isInvModel hc
  let M₃ := M₂.restrict a₃
  have hm₃ := hm₂.comp (M₂.τ a₃)
  have hu₃ := hu₂.comp (M₂.τ a₃)
  -- the axioms hold after base change to the limit, hence at a later stage
  let m₃ := Functor.LaxMonoidal.μ (Over.pullback (D.map a₃)) M₂.X M₂.X ≫
    (Over.pullback (D.map a₃)).map
      (Functor.LaxMonoidal.μ (Over.pullback (D.map a₂)) M₁.X M₁.X ≫
        (Over.pullback (D.map a₂)).map m₁)
  let u₃ := Functor.LaxMonoidal.ε (Over.pullback (D.map a₃)) ≫ (Over.pullback (D.map a₃)).map u₂
  have hX := M₃.finitePresentation
  have h1 := finitePresentation_tensorUnit_hom (D.obj k₃)
  have hXX := finitePresentation_tensorObj_hom hX hX
  obtain ⟨k, b, hb⟩ := (((((RelationModel.eventuallyBelow_map_eq hc
      (finitePresentation_tensorObj_hom h1 hX) hX (hm₃.map_one_mul hu₃)).and
    (RelationModel.eventuallyBelow_map_eq hc (finitePresentation_tensorObj_hom hX h1) hX
      (hm₃.map_mul_one hu₃))).and
    (RelationModel.eventuallyBelow_map_eq hc (finitePresentation_tensorObj_hom hXX hX) hX
      hm₃.map_mul_assoc)).and
    (RelationModel.eventuallyBelow_map_eq hc hX hX (hm₃.map_left_inv hu₃ hi₃))).and
    (RelationModel.eventuallyBelow_map_eq hc hX hX (hm₃.map_right_inv hu₃ hi₃))).and
    (RelationModel.eventuallyBelow_map_eq hc hXX hX hm₃.map_mul_comm)
  obtain ⟨⟨⟨⟨⟨f₁, f₂⟩, f₃⟩, f₄⟩, f₅⟩, f₆⟩ := hb (𝟙 k)
  rw [Category.id_comp] at f₁ f₂ f₃ f₄ f₅ f₆
  -- the group scheme at the final stage
  let G := Over.pullback (D.map b)
  let := grpObjOfMap G m₃ u₃ i₃ f₁ f₂ f₃ f₄ f₅
  have h𝒜 : IsCommMonObj (G.obj M₃.X) := isCommMonObj_grpObjOfMap G m₃ u₃ i₃ f₁ f₂ f₃ f₄ f₅ f₆
  let 𝒜 : Grp (Over (D.obj k)) := ⟨G.obj M₃.X⟩
  let M := M₃.restrict b
  exact ⟨k, b ≫ a₃ ≫ a₂ ≫ a₁ ≫ IsCofiltered.minToRight Mᵢ.stage j₀, 𝒜, h𝒜, M.e,
    M.finitePresentation, M.isSeparated,
    isMonHom_of_isMulModel 𝒜 (hm₃.comp (M₃.τ b)) (hu₃.comp (M₃.τ b))⟩

/-- **Spreading out a commutative group scheme over a cofiltered limit.** Let `S = lim Sᵢ` be a
cofiltered limit of quasi-compact quasi-separated schemes with affine transition morphisms, and
let `A` be a commutative group scheme over `S`, separated and of finite presentation. Then there
are a stage `Sₖ`, a commutative group scheme `𝒜` over `Sₖ`, separated and of finite presentation,
and an isomorphism of group schemes from the base change of `𝒜` to `A`. -/
theorem exists_grpObj_model_of_isLimit (hc : IsLimit c) (A : Over c.pt) [GrpObj A]
    [IsCommMonObj A] (hA : FinitePresentation A.hom) [IsSeparated A.hom] :
    ∃ (k : I) (𝒜 : Grp (Over (D.obj k))) (_ : IsCommMonObj 𝒜.X)
      (e : ((Over.pullback (c.π.app k)).mapGrp.obj 𝒜).X ≅ A),
      FinitePresentation 𝒜.X.hom ∧ IsSeparated 𝒜.X.hom ∧ IsMonHom e.hom := by
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨k, -, 𝒜, h𝒜, e, h⟩ := exists_grpObj_model_of_isLimit_of_hom hc A hA j₀
  exact ⟨k, 𝒜, h𝒜, e, h⟩

end Model

/-! ### Spreading out over a finitely generated subring of a field -/

/-- **Spreading out a commutative group scheme over a field.** Let `A` be a commutative group
scheme over a field `k`, separated and of finite presentation over `k`. Then there are a domain
`R` of finite type over `ℤ`, an injective ring homomorphism `ι : R →+* k`, a commutative group
scheme `𝒜` over `Spec R`, separated and of finite presentation, and an isomorphism of group
schemes from the base change of `𝒜` along `Spec k ⟶ Spec R` to `A`. The ring `R` is the
subring of `k` generated by a finite subset, and `ι` its inclusion. -/
theorem exists_grpObj_model {k : Type u} [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsCommMonObj A] [LocallyOfFinitePresentation A.hom] [QuasiCompact A.hom]
    [IsSeparated A.hom] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra.FiniteType ℤ R) (ι : R →+* k)
      (_ : Function.Injective ι) (𝒜 : Grp (Over (Spec (.of R)))) (_ : IsCommMonObj 𝒜.X)
      (e : ((Over.pullback (Spec.map (CommRingCat.ofHom ι))).mapGrp.obj 𝒜).X ≅ A),
      LocallyOfFinitePresentation 𝒜.X.hom ∧ QuasiCompact 𝒜.X.hom ∧ IsSeparated 𝒜.X.hom ∧
        IsMonHom e.hom := by
  have hA : FinitePresentation A.hom := ⟨inferInstance, inferInstance, inferInstance⟩
  let A' : Over (specAdjoinFinsetCone k).pt := A
  let : GrpObj A' := ‹GrpObj A›
  have : IsCommMonObj A' := ‹IsCommMonObj A›
  have : IsSeparated A'.hom := ‹IsSeparated A.hom›
  obtain ⟨s, 𝒜, h𝒜, e, hfp, hsep, he⟩ :=
    exists_grpObj_model_of_isLimit (isLimit_specAdjoinFinsetCone k) A' hA
  let R := Algebra.adjoin ℤ ((s.unop : Finset k) : Set k)
  exact ⟨R, inferInstance, inferInstance, finiteType_adjoinFinset_int k s.unop,
    R.val.toRingHom, Subtype.val_injective, 𝒜, h𝒜, e, hfp.1, hfp.2.1, hsep, he⟩

/-- **Spreading out a commutative group scheme over a field, over a subring containing given
elements.** Let `A` be a commutative group scheme over a field `k`, separated and of finite
presentation over `k`, and let `t ⊆ k` be finite. Then there are a domain `R` of finite type over
`ℤ`, an injective ring homomorphism `ι : R →+* k` whose image contains `t`, a commutative group
scheme `𝒜` over `Spec R`, separated and of finite presentation, and an isomorphism of group
schemes from the base change of `𝒜` along `Spec k ⟶ Spec R` to `A`. -/
theorem exists_grpObj_model_of_finset {k : Type u} [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsCommMonObj A] [LocallyOfFinitePresentation A.hom] [QuasiCompact A.hom]
    [IsSeparated A.hom] (t : Finset k) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra.FiniteType ℤ R) (ι : R →+* k)
      (_ : Function.Injective ι) (𝒜 : Grp (Over (Spec (.of R)))) (_ : IsCommMonObj 𝒜.X)
      (e : ((Over.pullback (Spec.map (CommRingCat.ofHom ι))).mapGrp.obj 𝒜).X ≅ A),
      LocallyOfFinitePresentation 𝒜.X.hom ∧ QuasiCompact 𝒜.X.hom ∧ IsSeparated 𝒜.X.hom ∧
        IsMonHom e.hom ∧ ∀ x ∈ t, x ∈ Set.range ι := by
  have hA : FinitePresentation A.hom := ⟨inferInstance, inferInstance, inferInstance⟩
  let A' : Over (specAdjoinFinsetCone k).pt := A
  let : GrpObj A' := ‹GrpObj A›
  have : IsCommMonObj A' := ‹IsCommMonObj A›
  have : IsSeparated A'.hom := ‹IsSeparated A.hom›
  obtain ⟨s, hs, 𝒜, h𝒜, e, hfp, hsep, he⟩ :=
    exists_grpObj_model_of_isLimit_of_hom (isLimit_specAdjoinFinsetCone k) A' hA (.op t)
  let R := Algebra.adjoin ℤ ((s.unop : Finset k) : Set k)
  refine ⟨R, inferInstance, inferInstance, finiteType_adjoinFinset_int k s.unop,
    R.val.toRingHom, Subtype.val_injective, 𝒜, h𝒜, e, hfp.1, hfp.2.1, hsep, he, fun x hx => ?_⟩
  exact ⟨⟨x, Algebra.subset_adjoin (Finset.mem_coe.mpr (leOfHom hs.unop hx))⟩, rfl⟩

end AlgebraicGeometry
