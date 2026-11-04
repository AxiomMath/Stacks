module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Examples.Geometric.BaseSpectrum

/-!
# Deformations of a morphism of schemes

A flat family of morphisms of schemes over `𝒞_Λ` consists of a morphism `X ⟶ Y` of schemes
over the spectrum of an object of `𝒞_Λ`, with both structure morphisms flat. A morphism of
such families goes covariantly on the bases and contravariantly on the two schemes, and
records that the source and target of the smaller family are the base changes of the source
and target of the larger one. Forgetting everything but the base gives a functor to `𝒞_Λ`,
and base change makes that functor cofibered in groupoids.

A morphism of schemes over the residue field is such a family over the residue-field object,
and the deformation category of that morphism is the category of objects over it.

## Main definitions

* `Deformation.Examples.SchemeMorphismFamily`: a flat family of morphisms of schemes over an
  object of `𝒞_Λ`.
* `Deformation.Examples.SchemeMorphismFamily.Hom`: a base-change morphism of such families.
* `Deformation.Examples.schemeMorphismFamilyFunctor`: the functor to `𝒞_Λ`.
* `Deformation.Examples.schemeMorphismFamilySpecialFiber`: a morphism of schemes over the
  residue field, viewed as a flat family.
* `Deformation.Examples.schemeMorphismDeformationCategory`: deformations of a fixed morphism of
  schemes over the residue field.

## Main results

* `Deformation.Examples.schemeMorphismFamilyFunctor_cofiberedInGroupoids`: the functor to
  `𝒞_Λ` is cofibered in groupoids.

## Implementation notes

Flatness is imposed on each of the two structure morphisms to the base; the pullback condition
on a morphism of families is recorded separately for the source and for the target, the source
condition relative to the morphism of the family and the target condition relative to the map
of base spectra. Over the residue field both structure morphisms are automatically flat,
because the base is the spectrum of a field.

The deformation category is an abbreviation for a slice category, so clients use the existing
API of `CategoryTheory.Over` directly; its structure functor is inherited from the family
functor. Nothing here assumes the morphisms Noetherian or of finite type.

## References

* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation.Examples

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A flat family of morphisms of schemes over an object of `𝒞_Λ`. -/
@[stacks 0E3T "deformation_category_of_a_scheme_morphism"]
structure SchemeMorphismFamily (Λ : Type u) (k : Type v) [CommRing Λ] [Field k]
    [Algebra Λ k] where
  /-- The object of `𝒞_Λ` the family lives over. -/
  base : ArtinianLocalAlgCat.{u, v, v} Λ k
  /-- The source of the family of morphisms. -/
  source : Scheme.{v}
  /-- The target of the family of morphisms. -/
  target : Scheme.{v}
  /-- The morphism being deformed. -/
  morphism : source ⟶ target
  /-- The structure morphism of the source. -/
  sourceToBase : source ⟶ baseSpec base
  /-- The structure morphism of the target. -/
  targetToBase : target ⟶ baseSpec base
  /-- The morphism is a morphism over the base. -/
  over_base : morphism ≫ targetToBase = sourceToBase
  /-- The source is flat over the base. -/
  source_flat : Flat sourceToBase
  /-- The target is flat over the base. -/
  target_flat : Flat targetToBase

namespace SchemeMorphismFamily

/-- A cartesian morphism of flat families of morphisms of schemes, directed covariantly on the
bases. -/
@[ext, stacks 0E3T "deformation_category_of_a_scheme_morphism"]
structure Hom (P Q : SchemeMorphismFamily.{u, v} Λ k) where
  /-- The morphism of the bases. -/
  base : P.base ⟶ Q.base
  /-- The morphism of sources, in the opposite direction. -/
  source : Q.source ⟶ P.source
  /-- The morphism of targets, in the opposite direction. -/
  target : Q.target ⟶ P.target
  /-- The source of the second family is the base change of the source of the first. -/
  source_pullback : IsPullback Q.morphism source target P.morphism
  /-- The target of the second family is the base change of the target of the first. -/
  target_pullback : IsPullback target Q.targetToBase P.targetToBase (baseSpecMap base)

/-- Flat families of morphisms of schemes and their base-change morphisms form a category. -/
instance instCategory : Category (SchemeMorphismFamily.{u, v} Λ k) where
  Hom := Hom
  id P :=
    { base := 𝟙 P.base
      source := 𝟙 P.source
      target := 𝟙 P.target
      source_pullback := IsPullback.id_vert P.morphism
      target_pullback := by
        rw [baseSpecMap_id]
        exact IsPullback.id_horiz P.targetToBase }
  comp f g :=
    { base := f.base ≫ g.base
      source := g.source ≫ f.source
      target := g.target ≫ f.target
      source_pullback := g.source_pullback.paste_vert f.source_pullback
      target_pullback := by
        rw [baseSpecMap_comp]
        exact g.target_pullback.paste_horiz f.target_pullback }
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp
  assoc := by intros; ext <;> simp [Category.assoc]

end SchemeMorphismFamily

/-- The functor sending a flat family of morphisms of schemes to its object of `𝒞_Λ`. -/
@[stacks 0E3T "deformation_category_of_a_scheme_morphism", implicit_reducible]
def schemeMorphismFamilyFunctor :
    SchemeMorphismFamily.{u, v} Λ k ⥤ ArtinianLocalAlgCat.{u, v, v} Λ k where
  obj P := P.base
  map f := f.base
  map_id := by intro; rfl
  map_comp := by intros; rfl

/-- The functor `schemeMorphismFamilyFunctor` sends a family to its base. -/
@[simp]
theorem schemeMorphismFamilyFunctor_obj (P : SchemeMorphismFamily.{u, v} Λ k) :
    (schemeMorphismFamilyFunctor (Λ := Λ) (k := k)).obj P = P.base := rfl

/-- The functor `schemeMorphismFamilyFunctor` sends a morphism of families to its morphism of
bases. -/
@[simp]
theorem schemeMorphismFamilyFunctor_map {P Q : SchemeMorphismFamily.{u, v} Λ k} (f : P ⟶ Q) :
    (schemeMorphismFamilyFunctor (Λ := Λ) (k := k)).map f = f.base := rfl

/-- A morphism of schemes over the residue field, viewed as a flat family over the
residue-field object of `𝒞_Λ`. -/
def schemeMorphismFamilySpecialFiber {X Y : Scheme.{v}} (f : X ⟶ Y)
    (pX : X ⟶ baseSpec (residueFieldBase Λ k))
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
    (hf : f ≫ pY = pX) : SchemeMorphismFamily.{u, v} Λ k where
  base := residueFieldBase Λ k
  source := X
  target := Y
  morphism := f
  sourceToBase := pX
  targetToBase := pY
  over_base := hf
  source_flat := by
    have : Subsingleton (baseSpec (residueFieldBase Λ k)) := by
      change Subsingleton (Spec (.of k))
      infer_instance
    have : IsIntegral (baseSpec (residueFieldBase Λ k)) := by
      change IsIntegral (Spec (.of k))
      infer_instance
    infer_instance
  target_flat := by
    have : Subsingleton (baseSpec (residueFieldBase Λ k)) := by
      change Subsingleton (Spec (.of k))
      infer_instance
    have : IsIntegral (baseSpec (residueFieldBase Λ k)) := by
      change IsIntegral (Spec (.of k))
      infer_instance
    infer_instance

/-- Deformations of a fixed morphism of schemes over the residue field. -/
@[stacks 0E3T "deformation_category_of_a_scheme_morphism"]
abbrev schemeMorphismDeformationCategory {X Y : Scheme.{v}} (f : X ⟶ Y)
    (pX : X ⟶ baseSpec (residueFieldBase Λ k))
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
    (hf : f ≫ pY = pX) :=
  Over (schemeMorphismFamilySpecialFiber f pX pY hf)

/-! ### The family functor is cofibered in groupoids -/

private def baseChange (P : SchemeMorphismFamily.{u, v} Λ k)
    {B : ArtinianLocalAlgCat.{u, v, v} Λ k} (f : P.base ⟶ B) :
    SchemeMorphismFamily.{u, v} Λ k := by
  let b := baseSpecMap f
  let X := pullback P.sourceToBase b
  let Y := pullback P.targetToBase b
  let m : X ⟶ Y := pullback.map P.sourceToBase b P.targetToBase b
    P.morphism (𝟙 _) (𝟙 _) P.over_base.symm (by simp)
  refine
    { base := B
      source := X
      target := Y
      morphism := m
      sourceToBase := pullback.snd P.sourceToBase b
      targetToBase := pullback.snd P.targetToBase b
      over_base := ?_
      source_flat := by let := P.source_flat; infer_instance
      target_flat := by let := P.target_flat; infer_instance }
  dsimp [m, X, Y]
  simp only [pullback.map, pullback.lift_snd, Category.comp_id]

private theorem baseChange_source_pullback (P : SchemeMorphismFamily.{u, v} Λ k)
    {B : ArtinianLocalAlgCat.{u, v, v} Λ k} (f : P.base ⟶ B) :
    IsPullback (pullback.map P.sourceToBase (baseSpecMap f) P.targetToBase
        (baseSpecMap f) P.morphism (𝟙 _) (𝟙 _) P.over_base.symm (by simp))
      (pullback.fst P.sourceToBase (baseSpecMap f))
      (pullback.fst P.targetToBase (baseSpecMap f)) P.morphism := by
  refine IsPullback.of_right (h₂₂ := P.targetToBase) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback P.targetToBase (baseSpecMap f)).flip
  have hm : pullback.map P.sourceToBase (baseSpecMap f) P.targetToBase (baseSpecMap f)
      P.morphism (𝟙 _) (𝟙 _) P.over_base.symm (by simp) ≫
      pullback.snd P.targetToBase (baseSpecMap f) =
      pullback.snd P.sourceToBase (baseSpecMap f) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [hm, P.over_base]
  exact (IsPullback.of_hasPullback P.sourceToBase (baseSpecMap f)).flip

private def baseChangeHom (P : SchemeMorphismFamily.{u, v} Λ k)
    {B : ArtinianLocalAlgCat.{u, v, v} Λ k} (f : P.base ⟶ B) : P ⟶ baseChange P f where
  base := f
  source := pullback.fst P.sourceToBase (baseSpecMap f)
  target := pullback.fst P.targetToBase (baseSpecMap f)
  source_pullback := baseChange_source_pullback P f
  target_pullback := by unfold baseChange; exact IsPullback.of_hasPullback _ _

private theorem family_factor {P Q R : SchemeMorphismFamily.{u, v} Λ k}
    (φ : P ⟶ Q) (ψ : P ⟶ R) (g : Q.base ⟶ R.base) (h : φ.base ≫ g = ψ.base) :
    ∃! χ : Q ⟶ R, χ.base = g ∧ φ ≫ χ = ψ := by
  classical
  let b := baseSpecMap g
  have hbase : baseSpecMap ψ.base = b ≫ baseSpecMap φ.base := by
    rw [← baseSpecMap_comp, h]
  let targetMap : R.target ⟶ Q.target := φ.target_pullback.lift ψ.target
    (R.targetToBase ≫ b) (by
      calc
        ψ.target ≫ P.targetToBase = R.targetToBase ≫ baseSpecMap ψ.base :=
          ψ.target_pullback.w
        _ = R.targetToBase ≫ b ≫ baseSpecMap φ.base := by rw [hbase]
        _ = (R.targetToBase ≫ b) ≫ baseSpecMap φ.base := by simp [Category.assoc])
  let sourceMap : R.source ⟶ Q.source := φ.source_pullback.lift
    (R.morphism ≫ targetMap) ψ.source (by
      calc
        (R.morphism ≫ targetMap) ≫ φ.target = R.morphism ≫ ψ.target := by
          rw [Category.assoc, φ.target_pullback.lift_fst]
        _ = ψ.source ≫ P.morphism := ψ.source_pullback.w)
  have hsource : sourceMap ≫ Q.morphism = R.morphism ≫ targetMap :=
    φ.source_pullback.lift_fst _ _ _
  have hcompSource : sourceMap ≫ φ.source = ψ.source :=
    φ.source_pullback.lift_snd _ _ _
  have hcompTarget : targetMap ≫ φ.target = ψ.target :=
    φ.target_pullback.lift_fst _ _ _
  have hOuterSource : IsPullback R.morphism
      (sourceMap ≫ φ.source) (targetMap ≫ φ.target) P.morphism := by
    simpa only [hcompSource, hcompTarget] using ψ.source_pullback
  have hOuterTarget : IsPullback (targetMap ≫ φ.target) R.targetToBase
      P.targetToBase (baseSpecMap g ≫ baseSpecMap φ.base) := by
    rw [hcompTarget, ← hbase]
    exact ψ.target_pullback
  let χ : Q ⟶ R :=
    { base := g
      source := sourceMap
      target := targetMap
      source_pullback := hOuterSource.of_bot hsource.symm φ.source_pullback
      target_pullback := hOuterTarget.of_right
        (φ.target_pullback.lift_snd _ _ _) φ.target_pullback }
  refine ⟨χ, ⟨rfl, ?_⟩, ?_⟩
  · exact SchemeMorphismFamily.Hom.ext h hcompSource hcompTarget
  · intro χ' hχ'
    have htarget : χ'.target = targetMap := by
      apply φ.target_pullback.hom_ext
      · exact (congrArg SchemeMorphismFamily.Hom.target hχ'.2).trans hcompTarget.symm
      · calc
          χ'.target ≫ Q.targetToBase = R.targetToBase ≫ baseSpecMap g := by
            rw [χ'.target_pullback.w, hχ'.1]
          _ = targetMap ≫ Q.targetToBase := (φ.target_pullback.lift_snd _ _ _).symm
    have hsource : χ'.source = sourceMap := by
      apply φ.source_pullback.hom_ext
      · calc
          χ'.source ≫ Q.morphism = R.morphism ≫ χ'.target := χ'.source_pullback.w.symm
          _ = R.morphism ≫ targetMap := by rw [htarget]
          _ = sourceMap ≫ Q.morphism := (φ.source_pullback.lift_fst _ _ _).symm
      · exact (congrArg SchemeMorphismFamily.Hom.source hχ'.2).trans hcompSource.symm
    exact SchemeMorphismFamily.Hom.ext hχ'.1 hsource htarget

/-- The category of flat families of morphisms of schemes is cofibered in groupoids over
`𝒞_Λ`. -/
@[stacks 0E3T]
theorem schemeMorphismFamilyFunctor_cofiberedInGroupoids
    {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k] :
    IsCofiberedInGroupoids (schemeMorphismFamilyFunctor.{u, v} (Λ := Λ) (k := k)) := by
  let p := schemeMorphismFamilyFunctor.{u, v} (Λ := Λ) (k := k)
  show p.op.IsFiberedInGroupoids
  refine ⟨?_, ?_⟩
  · intro V U f x hx
    subst U
    let P : SchemeMorphismFamily.{u, v} Λ k := x.unop
    let Q := baseChange P f.unop
    let α : P ⟶ Q := baseChangeHom P f.unop
    have hLift : p.op.IsHomLift f α.op := by
      apply IsHomLift.of_fac' (p := p.op) f α.op rfl rfl
      show Opposite.op f.unop = f
      rfl
    exact ⟨Opposite.op Q, α.op, hLift⟩
  · intro x y z φ ψ f h
    let P : SchemeMorphismFamily.{u, v} Λ k := x.unop
    let Q : SchemeMorphismFamily.{u, v} Λ k := y.unop
    let R : SchemeMorphismFamily.{u, v} Λ k := z.unop
    let φ₀ : P ⟶ Q := φ.unop
    let ψ₀ : P ⟶ R := ψ.unop
    let g : Q.base ⟶ R.base := f.unop
    have hbase : φ₀.base ≫ g = ψ₀.base := by
      show (p.map φ₀) ≫ f.unop = p.map ψ₀
      exact congrArg Quiver.Hom.unop h
    obtain ⟨χ, ⟨hχbase, hχcomp⟩, hχuniq⟩ := family_factor φ₀ ψ₀ g hbase
    refine ⟨χ.op, ⟨?_, ?_⟩, ?_⟩
    · simpa [p, g] using congrArg Quiver.Hom.op hχbase
    · simpa [φ₀, ψ₀, P, Q, R] using congrArg Quiver.Hom.op hχcomp
    · intro χ' hχ'
      have hχ'eq : χ'.unop = χ := hχuniq χ'.unop (by
        constructor
        · have hm := congrArg Quiver.Hom.unop hχ'.1
          change (schemeMorphismFamilyFunctor (Λ := Λ) (k := k)).map χ'.unop = f.unop at hm
          rw [schemeMorphismFamilyFunctor_map] at hm
          show χ'.unop.base = f.unop
          exact hm
        · have hc := congrArg Quiver.Hom.unop hχ'.2
          show φ₀ ≫ χ'.unop = ψ₀
          simpa [φ₀, ψ₀, P, Q, R] using hc)
      simpa using congrArg Quiver.Hom.op hχ'eq

end Deformation.Examples

end
