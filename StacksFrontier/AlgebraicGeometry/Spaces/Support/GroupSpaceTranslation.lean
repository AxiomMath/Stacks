module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Translation on a group algebraic space, and properties at a point

Right translation by a section of a group algebraic space `G ⟶ B` is an automorphism of `G`
over `B` carrying the identity section to that section. Consequently any property of the
structure morphism which is local on the source and invariant under automorphisms of the
source over the target — unramifiedness at a point and quasi-finiteness at a point among
them — holds at the identity point exactly when it holds at the point given by the section.

## Main results

* `AlgebraicGeometry.Space.exists_translation_iso`: right translation by a global section is an
  automorphism fixing the structure morphism and carrying the identity point to the point of the
  section.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_precomp_iso`: the étale-chart condition of a
  property of scheme morphisms is unchanged by precomposing with an isomorphism of presheaves.
* `AlgebraicGeometry.Space.pointwiseProperty_precomp_iso`: the open-subspace condition defining
  a pointwise property is transported along an automorphism of the source which the morphism
  absorbs.
* `AlgebraicGeometry.Space.isUnramifiedAt_one_iff_at_section` and
  `AlgebraicGeometry.Space.isQuasiFiniteAt_one_iff_at_section`: the comparison at the identity
  and at the value of a section.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Precomposing with an isomorphism of presheaves does not change whether a property of
scheme morphisms holds on every commuting square of étale charts. -/
theorem holdsOnEveryEtaleChart_precomp_iso (P : MorphismProperty Scheme.{u})
    {F F' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ F') (f : F' ⟶ Y) :
    HoldsOnEveryEtaleChart B S hS P f ↔ HoldsOnEveryEtaleChart B S hS P (e.hom ≫ f) := by
  let Q := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
  exact ⟨fun hf U V a b h ha hb hab =>
      hf U V (a ≫ e.hom) b h ((Q.cancel_right_of_respectsIso a e.hom).2 ha) hb (by simpa using hab),
    fun hf U V a b h ha hb hab =>
      hf U V (a ≫ e.inv) b h ((Q.cancel_right_of_respectsIso a e.inv).2 ha) hb (by simpa using hab)⟩

/-- An automorphism `e` of the source which the morphism `f` absorbs, in the sense that
`e.hom ≫ f = f`, transports the open-subspace witness defining a pointwise property of `f`
from a point to its image under `e`. -/
theorem pointwiseProperty_precomp_iso (P : MorphismProperty Scheme.{u})
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (e : X ≅ X) (he : e.hom ≫ f = f)
    (x : points B S hS X) :
    (∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      ∃ x' : points B S hS U.toFunctor,
        pointsMap B S hS U.toFunctor U.ι x' = x ∧
          HoldsOnEveryEtaleChart B S hS P (U.ι ≫ f)) ↔
    (∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      ∃ x' : points B S hS U.toFunctor,
        pointsMap B S hS U.toFunctor U.ι x' = pointsMap B S hS X e.hom x ∧
          HoldsOnEveryEtaleChart B S hS P (U.ι ≫ f)) := by
  let Qopen : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have heInv : e.inv ≫ f = f := (Iso.inv_comp_eq e).2 he.symm
  have key : ∀ (ε : X ≅ X), ε.hom ≫ f = f →
      ∀ U : Subfunctor X, IsOpenSubspace B S hS U →
      ∀ x' : points B S hS U.toFunctor,
        HoldsOnEveryEtaleChart B S hS P (U.ι ≫ f) →
      ∃ V : Subfunctor X, IsOpenSubspace B S hS V ∧
        ∃ y : points B S hS V.toFunctor,
          pointsMap B S hS V.toFunctor V.ι y =
            pointsMap B S hS X ε.hom (pointsMap B S hS U.toFunctor U.ι x') ∧
            HoldsOnEveryEtaleChart B S hS P (V.ι ≫ f) := by
    intro ε hε U hU x' hf
    let V : Subfunctor X := Subfunctor.range (U.ι ≫ ε.hom)
    let β : U.toFunctor ⟶ V.toFunctor := Subfunctor.toRange (U.ι ≫ ε.hom)
    have hmono : Mono (U.ι ≫ ε.hom) := inferInstance
    have : IsIso β := inferInstance
    have hβ : β ≫ V.ι = U.ι ≫ ε.hom := Subfunctor.toRange_ι _
    have hVopen : Qopen V.ι := by
      rw [← (Iso.inv_comp_eq (asIso β)).2 hβ.symm]
      exact MorphismProperty.RespectsIso.precomp Qopen (asIso β).inv (U.ι ≫ ε.hom)
        (MorphismProperty.RespectsIso.postcomp Qopen ε.hom U.ι hU.2)
    have hfac : V.ι ≫ f = (asIso β).inv ≫ (U.ι ≫ f) :=
      (Iso.eq_inv_comp _).2 (by simp [reassoc_of% hβ, hε])
    refine ⟨V, ⟨isAlgebraicSpace_of_iso B S hS (asIso β) hU.1, hVopen⟩,
      pointsMap B S hS U.toFunctor β x', ?_, ?_⟩
    · rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hβ]
    · rw [hfac]
      exact (holdsOnEveryEtaleChart_precomp_iso B S hS P (asIso β).symm (U.ι ≫ f)).mp hf
  constructor
  · rintro ⟨U, hU, x', hx', hf⟩
    obtain ⟨V, hV, y, hy, hVf⟩ := key e he U hU x' hf
    exact ⟨V, hV, y, by rw [hy, hx'], hVf⟩
  · rintro ⟨U, hU, x', hx', hf⟩
    obtain ⟨V, hV, y, hy, hVf⟩ := key e.symm heInv U hU x' hf
    refine ⟨V, hV, y, ?_, hVf⟩
    rw [hy, hx']
    rw [show e.symm.hom = e.inv from rfl, ← pointsMap_comp_apply, e.hom_inv_id,
      pointsMap_id]
    rfl

section Translation

variable {Bs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hBs : IsAlgebraicSpace B S hS Bs}

/-- Right translation by a global section of a group algebraic space is an automorphism of the
underlying presheaf which fixes the structure morphism and carries the identity point of the
base to the point determined by the section. -/
theorem exists_translation_iso (G : GroupAlgebraicSpace B S hS Bs hBs)
    (g : Over.mk (𝟙 Bs) ⟶ G.obj.X) (b : points B S hS Bs) :
    ∃ e : G.obj.X.left ≅ G.obj.X.left, e.hom ≫ G.obj.X.hom = G.obj.X.hom ∧
      pointsMap B S hS G.obj.X.left e.hom
          (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b) =
        pointsMap B S hS Bs g.left b := by
  let α := GrpObj.mulRight (A := G.obj.X) g
  refine ⟨(Over.forget Bs).mapIso α, α.hom.w, ?_⟩
  have hunit : MonObj.one (X := G.obj.X) ≫ α.hom = g := by
    dsimp [α, GrpObj.mulRight]
    rw [← Category.assoc, comp_lift]
    have hηunit : MonObj.one (X := G.obj.X) ≫ toUnit G.obj.X = 𝟙 (𝟙_ (Over Bs)) := by
      subsingleton
    simp only [Category.comp_id]
    rw [← Category.assoc, hηunit]
    simpa using MonObj.lift_comp_one_left (A := 𝟙_ (Over Bs)) (B := G.obj.X)
      (𝟙 (𝟙_ (Over Bs))) g
  rw [← pointsMap_comp_apply]
  congr 2
  exact congrArg (fun q : Over.mk (𝟙 Bs) ⟶ G.obj.X => q.left) hunit

/-- The structure morphism of a group algebraic space is unramified at the identity point over a
point of the base exactly when it is unramified at the point determined by a global section
there. -/
theorem isUnramifiedAt_one_iff_at_section (G : GroupAlgebraicSpace B S hS Bs hBs)
    (g : Over.mk (𝟙 Bs) ⟶ G.obj.X) (b : points B S hS Bs) :
    IsUnramifiedAt B S hS G.obj.X.hom
        (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b) ↔
      IsUnramifiedAt B S hS G.obj.X.hom (pointsMap B S hS Bs g.left b) := by
  obtain ⟨e, he, hpoint⟩ := exists_translation_iso B S hS G g b
  rw [show IsUnramifiedAt B S hS G.obj.X.hom
      (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b) ↔ _ from
    pointwiseProperty_precomp_iso B S hS
      (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
      G.obj.X.hom e he _, hpoint]

/-- The structure morphism of a group algebraic space is quasi-finite at the identity point over
a point of the base exactly when it is quasi-finite at the point determined by a global section
there. -/
theorem isQuasiFiniteAt_one_iff_at_section (G : GroupAlgebraicSpace B S hS Bs hBs)
    (g : Over.mk (𝟙 Bs) ⟶ G.obj.X) (b : points B S hS Bs) :
    IsQuasiFiniteAt B S hS G.obj.X.hom
        (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b) ↔
      IsQuasiFiniteAt B S hS G.obj.X.hom (pointsMap B S hS Bs g.left b) := by
  obtain ⟨e, he, hpoint⟩ := exists_translation_iso B S hS G g b
  rw [show IsQuasiFiniteAt B S hS G.obj.X.hom
      (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b) ↔ _ from
    pointwiseProperty_precomp_iso B S hS
      ((@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@_root_.AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      G.obj.X.hom e he _, hpoint]

end Translation

end AlgebraicGeometry.Space

end
