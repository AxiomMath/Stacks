module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# The spaces-étale site of an algebraic space (Stacks 03G0)

For an algebraic space `X` over a scheme `S`, the *spaces-étale site* of `X` has as objects
the algebraic spaces étale over `X` and as morphisms the commutative triangles over `X`. A
family covers when the images of its members jointly cover the points of its target.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleOver` is the property of an algebraic space over `X` that
  its structure morphism is étale.
* `AlgebraicGeometry.Space.SpacesEtale` is the category of algebraic spaces étale over `X`:
  **Stacks 03G0**.
* `AlgebraicGeometry.Space.SpacesEtale.IsCovering` is the point-surjective covering predicate
  and `AlgebraicGeometry.Space.SpacesEtale.topology` the Grothendieck topology it generates.
* `AlgebraicGeometry.Space.etaleMorphisms` is étaleness as a `MorphismProperty` of the
  category of algebraic spaces over `S`, which is what exhibits the spaces-étale site as
  `(AlgebraicGeometry.Space.etaleMorphisms B S hS).overObj`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isSite`: the point-surjective étale families satisfy
  the site axioms.
* `AlgebraicGeometry.Space.SpacesEtale.mem_precoverage_iff` characterizes the presented
  precoverage.
* `AlgebraicGeometry.Space.SpacesEtale.hasPullbacks`,
  `AlgebraicGeometry.Space.SpacesEtale.hasTerminal`,
  `AlgebraicGeometry.Space.SpacesEtale.inclusion_preservesPullbacks` and
  `AlgebraicGeometry.Space.SpacesEtale.inclusion_preservesTerminalShape`: **Stacks 0DF3**, the
  finite limits of the spaces-étale site and their preservation by the inclusion.

## Implementation notes

The category is the full subcategory of the slice of algebraic spaces over `X` on the objects
whose structure morphism is étale, so its morphisms are exactly the triangles over `X` that
the source specifies, and the full-subcategory API applies to them.

The covering predicate uses the points of an algebraic space of Tag 03BU — field-valued
points modulo common field extension — which is the existing model of the underlying
topological set of an algebraic space; this way geometric-point and sheaf clients need no
second notion of underlying space. The chosen covering families are all families at the
ambient index universe of the site that are jointly surjective on points.

The three site axioms are: the isomorphism axiom, from functoriality of points; the
composition axiom, by composing the two liftings of a point; and the base change axiom, where
the fibre product is the fibre product of algebraic spaces (Tag 043C), étale over `X` by Tag
03FV, Tag 03FU and Tag 03FT, cartesian in the small site because the inclusion into the slice
and the forgetful functor of the slice both reflect it, and jointly surjective by Tag 03H4.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- The property of an algebraic space over `X` that its structure morphism to `X` is
étale. -/
abbrev IsEtaleOver : ObjectProperty (Over X) :=
  fun U ↦ IsEtale B S hS U.hom.hom

/-- **Stacks 03G0.** The spaces-étale site of `X`: the category of algebraic spaces étale over
`X`, with the commutative triangles over `X` as morphisms. -/
@[stacks 03G0 "objects and morphisms"]
abbrev SpacesEtale := (IsEtaleOver B S hS X).FullSubcategory

namespace SpacesEtale

/-- The inclusion of the spaces-étale site of `X` into all algebraic spaces over `X`. -/
abbrev inclusion : SpacesEtale B S hS X ⥤ Over X := (IsEtaleOver B S hS X).ι

/-- The underlying algebraic space of an object étale over `X`. -/
abbrev toSpaces : SpacesEtale B S hS X ⥤ AlgebraicSpaces B S hS :=
  inclusion B S hS X ⋙ Over.forget X

private theorem pointsMap_toSpaces_comp {A C D : SpacesEtale B S hS X} (f : A ⟶ C) (g : C ⟶ D)
    (x : points B S hS ((toSpaces B S hS X).obj A).1) :
    pointsMap B S hS ((toSpaces B S hS X).obj A).1 ((toSpaces B S hS X).map (f ≫ g)).hom x =
      pointsMap B S hS ((toSpaces B S hS X).obj C).1 ((toSpaces B S hS X).map g).hom
        (pointsMap B S hS ((toSpaces B S hS X).obj A).1
          ((toSpaces B S hS X).map f).hom x) := by
  simp

private theorem pointsMap_toSpaces_inv {A C : SpacesEtale B S hS X} (f : A ⟶ C) [IsIso f]
    (x : points B S hS ((toSpaces B S hS X).obj C).1) :
    pointsMap B S hS ((toSpaces B S hS X).obj A).1 ((toSpaces B S hS X).map f).hom
        (pointsMap B S hS ((toSpaces B S hS X).obj C).1
          ((toSpaces B S hS X).map (inv f)).hom x) = x := by
  have hmaps : ((toSpaces B S hS X).map (inv f)).hom ≫ ((toSpaces B S hS X).map f).hom = 𝟙 _ := by
    have hcat : (toSpaces B S hS X).map (inv f) ≫ (toSpaces B S hS X).map f =
        𝟙 ((toSpaces B S hS X).obj C) := by
      rw [← Functor.map_comp]
      simp
    simp
  have hcomp := congrFun (pointsMap_comp B S hS ((toSpaces B S hS X).obj C).1
    ((toSpaces B S hS X).map (inv f)).hom ((toSpaces B S hS X).map f).hom) x
  simpa only [hmaps, pointsMap_id, id_eq, Function.comp_apply] using hcomp.symm

/-- **Stacks 03G0.** A family in the spaces-étale site of `X` covers when every point of its
target lifts to a point of some member of the family. -/
@[stacks 03G0 "coverings"]
abbrev IsCovering (E : Covering (SpacesEtale B S hS X)) : Prop :=
  ∀ x : points B S hS ((toSpaces B S hS X).obj E.1).1,
    ∃ i : E.2.I₀, ∃ y : points B S hS ((toSpaces B S hS X).obj (E.2.X i)).1,
      pointsMap B S hS ((toSpaces B S hS X).obj (E.2.X i)).1
        ((toSpaces B S hS X).map (E.2.f i)).hom y = x

/-- The precoverage presented by the jointly point-surjective families of the spaces-étale
site of `X`. -/
def precoverage : Precoverage (SpacesEtale B S hS X) where
  coverings U := {R | ∃ E : PreZeroHypercover.{u + 1} U,
    R = E.presieve₀ ∧ IsCovering B S hS X ⟨U, E⟩}

/-- A presieve belongs to the precoverage of the spaces-étale site of `X` exactly when it is
presented by a jointly point-surjective family. -/
theorem mem_precoverage_iff {U : SpacesEtale B S hS X} {R : Presieve U} :
    R ∈ precoverage B S hS X U ↔
      ∃ E : PreZeroHypercover.{u + 1} U, R = E.presieve₀ ∧ IsCovering B S hS X ⟨U, E⟩ :=
  Iff.rfl

/-- The Grothendieck topology of the spaces-étale site of `X`, generated by the jointly point-
surjective families. -/
abbrev topology : GrothendieckTopology (SpacesEtale B S hS X) :=
  (precoverage B S hS X).toGrothendieck

/-- **Stacks 03G0.** Joint surjectivity on points of families in the spaces-étale site of `X`
satisfies the site axioms. -/
@[stacks 03G0 "site axioms"]
theorem isSite : IsSite (IsCovering B S hS X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    have _ : IsIso f := hf
    intro x
    exact ⟨⟨⟩, pointsMap B S hS ((toSpaces B S hS X).obj U).1
      ((toSpaces B S hS X).map (inv f)).hom x, pointsMap_toSpaces_inv B S hS X f x⟩
  · intro E hE F hF htarget x
    obtain ⟨i, y, hy⟩ := hE x
    let e : (F i).1 ⟶ E.2.X i := eqToHom (htarget i)
    obtain ⟨j, z, hz⟩ := hF i (pointsMap B S hS ((toSpaces B S hS X).obj (E.2.X i)).1
      ((toSpaces B S hS X).map (inv e)).hom y)
    refine ⟨⟨i, j⟩, z, ?_⟩
    change pointsMap B S hS ((toSpaces B S hS X).obj ((F i).2.X j)).1
      ((toSpaces B S hS X).map (((F i).2.f j ≫ e) ≫ E.2.f i)).hom z = x
    calc
      _ = pointsMap B S hS ((toSpaces B S hS X).obj (E.2.X i)).1
            ((toSpaces B S hS X).map (E.2.f i)).hom
            (pointsMap B S hS ((toSpaces B S hS X).obj (F i).1).1
              ((toSpaces B S hS X).map e).hom
              (pointsMap B S hS ((toSpaces B S hS X).obj ((F i).2.X j)).1
                ((toSpaces B S hS X).map ((F i).2.f j)).hom z)) := by
            simp only [pointsMap_toSpaces_comp]
      _ = pointsMap B S hS ((toSpaces B S hS X).obj (E.2.X i)).1
            ((toSpaces B S hS X).map (E.2.f i)).hom y := by
            rw [hz, pointsMap_toSpaces_inv]
      _ = x := hy
  · intro E hE V g
    let α (i : E.2.I₀) := (toSpaces B S hS X).map (E.2.f i)
    let β := (toSpaces B S hS X).map g
    let W (i : E.2.I₀) := AlgebraicSpaces.fiberProduct B S hS (α i) β
    let p₁ (i : E.2.I₀) : W i ⟶ (toSpaces B S hS X).obj (E.2.X i) :=
      ObjectProperty.homMk (pullback.fst (α i).hom β.hom)
    let p₂ (i : E.2.I₀) : W i ⟶ (toSpaces B S hS X).obj V :=
      ObjectProperty.homMk (pullback.snd (α i).hom β.hom)
    have hpb (i : E.2.I₀) : IsPullback (p₁ i) (p₂ i) (α i) β := by
      simpa [p₁, p₂, W, α, β] using AlgebraicSpaces.isPullback_fiberProduct B S hS (α i) β
    let vOver := (inclusion B S hS X).obj V
    let zOver (i : E.2.I₀) : Over X := Over.mk (p₂ i ≫ vOver.hom)
    have hfg {A C : SpacesEtale B S hS X} (f : A ⟶ C) :
        (toSpaces B S hS X).map f ≫ ((inclusion B S hS X).obj C).hom =
          ((inclusion B S hS X).obj A).hom := by
      simp [toSpaces, inclusion]
    have hp (i : E.2.I₀) : IsEtaleOver B S hS X (zOver i) := by
      have hα : IsEtale B S hS (α i).hom :=
        isEtale_of_isEtale_over B S hS
          ((toSpaces B S hS X).obj (E.2.X i)).property
          ((toSpaces B S hS X).obj E.1).property X.property
          (α i).hom ((inclusion B S hS X).obj (E.2.X i)).hom.hom
          ((inclusion B S hS X).obj E.1).hom.hom
          (E.2.X i).property E.1.property (congrArg (fun k ↦ k.hom) (hfg (E.2.f i)))
      have hp₂ : IsEtale B S hS (p₂ i).hom :=
        isEtale_of_isPullback B S hS (p₁ i) (p₂ i) (α i) β (hpb i) hα
      have hv : IsEtale B S hS vOver.hom.hom := V.property
      change IsEtale B S hS (p₂ i ≫ vOver.hom).hom
      exact isEtale_comp B S hS hp₂ hv
    let P : E.2.I₀ → SpacesEtale B S hS X := fun i ↦ ⟨zOver i, hp i⟩
    let r₁ (i : E.2.I₀) : zOver i ⟶ (inclusion B S hS X).obj (E.2.X i) :=
      Over.homMk (p₁ i) (by
        change p₁ i ≫ ((inclusion B S hS X).obj (E.2.X i)).hom = p₂ i ≫ vOver.hom
        rw [← hfg (E.2.f i), ← Category.assoc, (hpb i).w, Category.assoc, hfg g])
    let r₂ (i : E.2.I₀) : zOver i ⟶ vOver := Over.homMk (p₂ i) rfl
    let π₁ (i : E.2.I₀) : P i ⟶ E.2.X i := ObjectProperty.homMk (r₁ i)
    let π₂ (i : E.2.I₀) : P i ⟶ V := ObjectProperty.homMk (r₂ i)
    refine ⟨P, π₁, π₂, ?_, ?_⟩
    · intro i
      have hcommOver : r₁ i ≫ (inclusion B S hS X).map (E.2.f i) =
          r₂ i ≫ (inclusion B S hS X).map g := Over.OverMorphism.ext (hpb i).w
      have hw : π₁ i ≫ E.2.f i = π₂ i ≫ g :=
        (inclusion B S hS X).map_injective hcommOver
      refine IsPullback.of_map (inclusion B S hS X) hw ?_
      refine IsPullback.of_map (Over.forget X) hcommOver ?_
      simpa [π₁, π₂, r₁, r₂, P, zOver, p₁, p₂, W, α, β, vOver] using hpb i
    · intro x
      obtain ⟨i, y, hy⟩ := hE (pointsMap B S hS ((toSpaces B S hS X).obj V).1 β.hom x)
      obtain ⟨w, -, hw₂⟩ := exists_point_of_isPullback B S hS (hpb i) y x hy
      exact ⟨i, w, by simpa [IsCovering, π₂, r₂, P, zOver, p₂, W, β] using hw₂⟩

end SpacesEtale

/-! ### Étaleness as a morphism property, and the finite limits it provides -/

/-- Étaleness of a morphism of algebraic spaces over `S` (Tag 03FR), as a property of
morphisms of the category of algebraic spaces over `S`. -/
abbrev etaleMorphisms : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ g ↦ IsEtale B S hS g.hom

/-- Étaleness of morphisms of algebraic spaces is multiplicative: identities are étale and
composites of étale morphisms are étale (Tag 03FT). -/
instance etaleMorphisms_isMultiplicative : (etaleMorphisms B S hS).IsMultiplicative where
  id_mem A := fun _ _ hφ ↦ by simpa using hφ
  comp_mem g h hg hh := isEtale_comp B S hS hg hh

/-- Étaleness of morphisms of algebraic spaces is stable under base change (Tag 03FU). -/
instance etaleMorphisms_isStableUnderBaseChange :
    (etaleMorphisms B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg :=
    isEtale_of_isPullback B S hS _ _ _ _ (by simpa [etaleMorphisms] using sq)
      (by simpa [etaleMorphisms] using hg)

/-- If a composite of morphisms of algebraic spaces and its second factor are étale, so is
its first factor (Tag 03FV). -/
instance etaleMorphisms_hasOfPostcompProperty :
    (etaleMorphisms B S hS).HasOfPostcompProperty (etaleMorphisms B S hS) where
  of_postcomp {A C D} g h hh hgh := by
    apply isEtale_of_isEtale_over B S hS A.property C.property D.property
      g.hom (g.hom ≫ h.hom) h.hom
    · simpa [etaleMorphisms] using hgh
    · simpa [etaleMorphisms] using hh
    · simp

/-- The base scheme itself, as an object of the big fppf site of `S`. -/
abbrev baseTerminal : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The presheaf represented by the base scheme is the final presheaf on the big fppf site
of `S`. -/
noncomputable def baseTerminal_yonedaIsTerminal :
    IsTerminal (yoneda.obj (baseTerminal B S hS)) :=
  (Over.mkIdTerminal : IsTerminal (baseTerminal B S hS)).isTerminalObj yoneda

/-- The base scheme itself, as an algebraic space over `S`. -/
noncomputable def terminalSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (baseTerminal B S hS), isAlgebraicSpace_yoneda B S hS (baseTerminal B S hS)⟩

/-- There is exactly one morphism from any algebraic space over `S` to the base scheme. -/
noncomputable instance terminalSpace_unique (A : AlgebraicSpaces B S hS) :
    Unique (A ⟶ terminalSpace B S hS) where
  default := ObjectProperty.homMk ((baseTerminal_yonedaIsTerminal B S hS).from A.1)
  uniq _ := ObjectProperty.hom_ext _ ((baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _)

/-- The base scheme is the final algebraic space over `S`. -/
noncomputable def terminalSpace_isTerminal : IsTerminal (terminalSpace B S hS) :=
  haveI : ∀ A : AlgebraicSpaces B S hS, Unique (A ⟶ terminalSpace B S hS) :=
    terminalSpace_unique B S hS
  IsTerminal.ofUnique _

/-- The category of algebraic spaces over `S` has a final object. -/
noncomputable instance algebraicSpaces_hasTerminal : HasTerminal (AlgebraicSpaces B S hS) :=
  (terminalSpace_isTerminal B S hS).hasTerminal

/-- The category of algebraic spaces over `S` has equalizers. -/
noncomputable instance algebraicSpaces_hasEqualizers :
    HasEqualizers (AlgebraicSpaces B S hS) :=
  have _ : HasBinaryProducts (AlgebraicSpaces B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  hasEqualizers_of_hasPullbacks_and_binary_products

namespace SpacesEtale

/-- **Stacks 0DF3.** The spaces-étale site of `X` has fibre products: it is the full
subcategory of the slice over `X` cut out by a base-change stable property of morphisms, so a
fibre product of algebraic spaces étale over `X` is again étale over `X`. -/
@[stacks 0DF3 "fibre products in the small site"]
instance hasPullbacks : HasPullbacks (SpacesEtale B S hS X) := by
  change HasPullbacks ((etaleMorphisms B S hS).overObj (X := X)).FullSubcategory
  infer_instance

/-- The identity of `X`, as an object of the spaces-étale site of `X`. -/
noncomputable def final : SpacesEtale B S hS X :=
  ⟨Over.mk (𝟙 X), (etaleMorphisms B S hS).id_mem X⟩

/-- There is exactly one morphism from any object of the spaces-étale site of `X` to the
identity of `X`. -/
noncomputable instance final_unique (A : SpacesEtale B S hS X) :
    Unique (A ⟶ final B S hS X) where
  default := ObjectProperty.homMk (Over.mkIdTerminal.from A.1)
  uniq _ := ObjectProperty.hom_ext _ (Over.mkIdTerminal.hom_ext _ _)

/-- The identity of `X` is the final object of the spaces-étale site of `X`. -/
noncomputable def final_isTerminal : IsTerminal (final B S hS X) :=
  haveI : ∀ A : SpacesEtale B S hS X, Unique (A ⟶ final B S hS X) := final_unique B S hS X
  IsTerminal.ofUnique _

/-- **Stacks 0DF3.** The spaces-étale site of `X` has a final object, the identity of `X`. -/
@[stacks 0DF3 "the final object of the small site"]
noncomputable instance hasTerminal : HasTerminal (SpacesEtale B S hS X) :=
  (final_isTerminal B S hS X).hasTerminal

/-- The spaces-étale site of `X` has equalizers. -/
noncomputable instance hasEqualizers : HasEqualizers (SpacesEtale B S hS X) :=
  have _ : HasBinaryProducts (SpacesEtale B S hS X) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  hasEqualizers_of_hasPullbacks_and_binary_products

/-- The inclusion of the spaces-étale site of `X` into the slice over `X` sends the identity
of `X` to a final object, hence preserves the final object. -/
noncomputable instance inclusion_preservesTerminal :
    PreservesLimit (Functor.empty.{0} (SpacesEtale B S hS X)) (inclusion B S hS X) := by
  apply preservesTerminal_of_iso _
  have ht : IsTerminal ((inclusion B S hS X).obj (final B S hS X)) := by
    simpa [final, inclusion] using (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 X)))
  exact (inclusion B S hS X).mapIso
      ((terminalIsTerminal (C := SpacesEtale B S hS X)).uniqueUpToIso
        (final_isTerminal B S hS X)) ≪≫
    ht.uniqueUpToIso (terminalIsTerminal (C := Over X))

/-- **Stacks 0DF3.** The final object of the spaces-étale site of `X` remains final in the
slice over `X`. -/
@[stacks 0DF3 "the inclusion preserves the final object"]
noncomputable instance inclusion_preservesTerminalShape :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (inclusion B S hS X) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- **Stacks 0DF3.** The inclusion of the spaces-étale site of `X` into the slice over `X`
preserves fibre products. -/
@[stacks 0DF3 "the inclusion preserves fibre products"]
instance inclusion_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (inclusion B S hS X) := by
  change PreservesLimitsOfShape WalkingCospan
    ((etaleMorphisms B S hS).overObj (X := X)).ι
  infer_instance

/-- The inclusion of the spaces-étale site of `X` into the slice over `X` preserves
equalizers. -/
noncomputable instance inclusion_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (inclusion B S hS X) :=
  have _ : HasFiniteLimits (SpacesEtale B S hS X) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have _ : PreservesFiniteLimits (inclusion B S hS X) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  inferInstance

end SpacesEtale

end AlgebraicGeometry.Space

end
