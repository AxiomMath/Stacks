module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Homology.Tor.IndependenceBaseChange

/-!
# The derived base-change comparison of a pasting of two squares

Let

```
R --f--> A
|        |
g₁       h₁
v        v
R' --i₁-> A'
|        |
g₂       h₂
v        v
R'' -i₂-> A''
```

be two commutative squares of commutative rings stacked on top of one another.  Tag 065Z
attaches to each commutative square a natural comparison `K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'`, and this file
proves that the comparison of the outer square is the composition of the comparisons of the two
inner squares, read through the composition isomorphisms
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` of derived extension of
scalars.

This is the one statement about Tag 065Z that a *localization* of a square needs: the four
localizations of a square at a prime of `A''` again form a commutative square, and the
localization maps make that square the second floor of a pasting as above, so compatibility of
the comparison with localizing a square is this pasting law at that particular second floor.

## Main definitions

* `RingTheory.TorIndependence.canonicalBaseChangeComparison`: the comparison of Tag 065Z at the
  canonical choice of total derived extension-of-scalars functors,
  `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`.
* `RingTheory.TorIndependence.canonicalUnderivedBaseChangeComparison`: its underived companion,
  the first component of `RingTheory.TorIndependence.derivedBaseChangeComparison`.

## Main results

* `RingTheory.TorIndependence.canonicalUnderivedBaseChangeComparison_tmul`: the underived
  comparison on a pure tensor.
* `RingTheory.TorIndependence.canonicalBaseChangeComparison_counit`: the counit equation, and
  `RingTheory.TorIndependence.canonicalBaseChangeComparison_eq_of_counit`: it determines the
  comparison.
* `RingTheory.TorIndependence.canonicalUnderivedBaseChangeComparison_paste`: the pasting law for
  the underived comparison.
* **`RingTheory.TorIndependence.canonicalBaseChangeComparison_paste`: the pasting law for the
  comparison of Tag 065Z.**

## Implementation notes

The model of the derived category is free: a single universe `w` serves as the model universe of
all six rings, as it does in the ring layer of Stacks 0DJ8.  Fixing one universe for all six is
what lets the statements of
`StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations` be applied with their
universe arguments written out, which is unavoidable because the comparison's own signature takes
the two derived functors and their comparison maps as parameters and so determines no universe by
unification.

*Why the proof goes through an abstract diagram lemma.*  A morphism such as
`Functor.mapDerivedCategoryFactors.hom.app K` has a type written with `Functor.comp`, while the
morphism it is composed with has the same type written with the composite applied by hand.  The
two agree only after unfolding `CategoryTheory.Functor.comp`, so a composite containing one of
them is not type-correct at `implicit` transparency and `rw` and `simp` refuse to fire on it.
`RingTheory.TorIndependence.pasteDiagram` therefore states the whole chase for abstract objects
and morphisms of abstract categories, where no such unfolding is needed, and takes each equation
in exactly the shape the library provides it; the pasting law is then one application of it.

*What the chase is.*  At a K-flat complex the comparison of a square is determined by its counit
equation, so it is enough to check that equation for the pasted transformation.  Substituting the
counit equations of the two floors, the compatibility of the composition isomorphisms with the
comparison maps to degreewise extension of scalars, and the naturality of everything in sight
leaves exactly the underived pasting law, which is an identity between `R''`-linear maps checked
on the pure tensors `1 ⊗ m`.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

namespace RingTheory.TorIndependence

universe u w

/-! ### The comparison at the canonical derived functors -/

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]

/-- **The comparison of Tag 065Z at the canonical derived functors.** For a commutative square
`h.comp f = i.comp g` of commutative rings, the natural transformation

`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'`

of `RingTheory.TorIndependence.derivedBaseChangeComparison`, taken at the canonical choice
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` of total derived
extension-of-scalars functors. -/
public abbrev canonicalBaseChangeComparison
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g) :
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} h).functor ⋙
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, w, w, w, w} R A R' A' _ _ _ _ _ _ _ _
    f g h i sq
    (totalDerivedExtensionScalars.{u, u, u} g).functor
    (totalDerivedExtensionScalars.{u, u, u} h).functor
    (totalDerivedExtensionScalars.{u, u, u} g).comparison
    (totalDerivedExtensionScalars.{u, u, u} h).comparison
    (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} h).isLeftDerived).2.1

/-- **The underived comparison of Tag 065Z at the canonical derived functors**, the first
component of `RingTheory.TorIndependence.derivedBaseChangeComparison`: the natural
transformation `R' ⊗_R M ⟶ A' ⊗_A M` of `R'`-modules attached to a commutative square. -/
public abbrev canonicalUnderivedBaseChangeComparison
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g) :
    ModuleCat.restrictScalars.{u} f ⋙ ModuleCat.extendScalars.{u, u, u} g ⟶
      ModuleCat.extendScalars.{u, u, u} h ⋙ ModuleCat.restrictScalars.{u} i :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, w, w, w, w} R A R' A' _ _ _ _ _ _ _ _
    f g h i sq
    (totalDerivedExtensionScalars.{u, u, u} g).functor
    (totalDerivedExtensionScalars.{u, u, u} h).functor
    (totalDerivedExtensionScalars.{u, u, u} g).comparison
    (totalDerivedExtensionScalars.{u, u, u} h).comparison
    (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} h).isLeftDerived).1

/-- **The underived comparison on a pure tensor**: it carries `r' ⊗ m` to `i r' ⊗ m`. -/
public theorem canonicalUnderivedBaseChangeComparison_tmul
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g) (M : ModuleCat.{u} A) (r' : R') (m : M) :
    (canonicalUnderivedBaseChangeComparison.{u, w} f g h i sq).app M (r' ⊗ₜ[R, g] m) =
      (i r') ⊗ₜ[A, h] m :=
  @derivedBaseChangeComparison_fst_app_tmul.{u, u, u, u, u, w, w, w, w}
    R A R' A' _ _ _ _ _ _ _ _ f g h i _ _ sq
    (totalDerivedExtensionScalars.{u, u, u} g).functor
    (totalDerivedExtensionScalars.{u, u, u} h).functor
    (totalDerivedExtensionScalars.{u, u, u} g).comparison
    (totalDerivedExtensionScalars.{u, u, u} h).comparison
    (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} h).isLeftDerived M r' m

/-- **The counit equation of the comparison**, at a complex: composing the comparison with the
counit of derived extension of scalars along `A → A'` and restricting along `R' → A'` is the
counit along `R → R'` followed by the underived comparison. -/
public theorem canonicalBaseChangeComparison_counit
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (canonicalBaseChangeComparison.{u, w} f g h i sq).app (DerivedCategory.Q.obj K) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, u} h).comparison.app K) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) =
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app K) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (canonicalUnderivedBaseChangeComparison.{u, w} f g h i sq)
          (ComplexShape.up ℤ)).app K) :=
  @derivedBaseChangeComparison_snd_app_comp_counit.{u, u, u, u, u, w, w, w, w}
    R A R' A' _ _ _ _ _ _ _ _ f g h i _ _ sq
    (totalDerivedExtensionScalars.{u, u, u} g).functor
    (totalDerivedExtensionScalars.{u, u, u} h).functor
    (totalDerivedExtensionScalars.{u, u, u} g).comparison
    (totalDerivedExtensionScalars.{u, u, u} h).comparison
    (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} h).isLeftDerived K

/-- **The counit equation determines the comparison.** A natural transformation satisfying the
equation of `RingTheory.TorIndependence.canonicalBaseChangeComparison_counit` at every K-flat
complex is the comparison. -/
public theorem canonicalBaseChangeComparison_eq_of_counit
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g)
    (tau : (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} h).functor ⋙
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory)
    (htau : ∀ K : CochainComplex (ModuleCat.{u} A) ℤ, CochainComplex.KFlat.{u, u} K →
      tau.app (DerivedCategory.Q.obj K) ≫
          (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
            ((totalDerivedExtensionScalars.{u, u, u} h).comparison.app K) ≫
          (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) =
        (totalDerivedExtensionScalars.{u, u, u} g).functor.map
            ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app K) ≫
          (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
            (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (canonicalUnderivedBaseChangeComparison.{u, w} f g h i sq)
            (ComplexShape.up ℤ)).app K)) :
    tau = canonicalBaseChangeComparison.{u, w} f g h i sq :=
  @derivedBaseChangeComparison_snd_eq.{u, u, u, u, u, w, w, w, w}
    R A R' A' _ _ _ _ _ _ _ _ f g h i _ _ sq
    (totalDerivedExtensionScalars.{u, u, u} g).functor
    (totalDerivedExtensionScalars.{u, u, u} h).functor
    (totalDerivedExtensionScalars.{u, u, u} g).comparison
    (totalDerivedExtensionScalars.{u, u, u} h).comparison
    (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} h).isLeftDerived tau htau

/-! ### The pasting law -/

variable {R'' A'' : Type u} [CommRing R''] [CommRing A'']
  [HasDerivedCategory.{w} (ModuleCat.{u} R'')] [HasDerivedCategory.{w} (ModuleCat.{u} A'')]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
  [HasDerivedCategory.{w} (ModuleCat.{u} R'')] [HasDerivedCategory.{w} (ModuleCat.{u} A'')] in
/-- **The outer square of a pasting of two commutative squares of rings commutes.** -/
public theorem comp_comp_eq_comp_comp
    (f : R →+* A) (g₁ : R →+* R') (h₁ : A →+* A') (i₁ : R' →+* A')
    (g₂ : R' →+* R'') (h₂ : A' →+* A'') (i₂ : R'' →+* A'')
    (sq₁ : h₁.comp f = i₁.comp g₁) (sq₂ : h₂.comp i₁ = i₂.comp g₂) :
    (h₂.comp h₁).comp f = i₂.comp (g₂.comp g₁) := by
  rw [RingHom.comp_assoc, sq₁, ← RingHom.comp_assoc, sq₂, RingHom.comp_assoc]

/-- **The pasting law for the underived comparison.** Extending scalars along `g₂` after the
comparison of the lower square, followed by the comparison of the upper square, is the comparison
of the outer square, read through the scalar-tower isomorphisms of extension of scalars. -/
public theorem canonicalUnderivedBaseChangeComparison_paste
    (f : R →+* A) (g₁ : R →+* R') (h₁ : A →+* A') (i₁ : R' →+* A')
    (g₂ : R' →+* R'') (h₂ : A' →+* A'') (i₂ : R'' →+* A'')
    (sq₁ : h₁.comp f = i₁.comp g₁) (sq₂ : h₂.comp i₁ = i₂.comp g₂)
    (sq : (h₂.comp h₁).comp f = i₂.comp (g₂.comp g₁)) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalarsComp.{u, u} g₁ g₂).hom.app
        ((ModuleCat.restrictScalars.{u} f).obj M) ≫
      (ModuleCat.extendScalars.{u, u, u} g₂).map
        ((canonicalUnderivedBaseChangeComparison.{u, w} f g₁ h₁ i₁ sq₁).app M) ≫
      (canonicalUnderivedBaseChangeComparison.{u, w} i₁ g₂ h₂ i₂ sq₂).app
        ((ModuleCat.extendScalars.{u, u, u} h₁).obj M) =
    (canonicalUnderivedBaseChangeComparison.{u, w} f (g₂.comp g₁) (h₂.comp h₁) i₂ sq).app M ≫
      (ModuleCat.restrictScalars.{u} i₂).map
        ((ModuleCat.extendScalarsComp.{u, u} h₁ h₂).hom.app M) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have h1 := canonicalUnderivedBaseChangeComparison_tmul.{u, w} f g₁ h₁ i₁ sq₁ M 1 m
  have h2 := canonicalUnderivedBaseChangeComparison_tmul.{u, w} i₁ g₂ h₂ i₂ sq₂
    ((ModuleCat.extendScalars.{u, u, u} h₁).obj M) 1 ((1 : A') ⊗ₜ[A, h₁] m)
  have h3 := canonicalUnderivedBaseChangeComparison_tmul.{u, w} f (g₂.comp g₁) (h₂.comp h₁) i₂
    sq M 1 m
  rw [map_one] at h1 h2 h3
  exact (((congrArg (fun y ↦
        (canonicalUnderivedBaseChangeComparison.{u, w} i₁ g₂ h₂ i₂ sq₂).app
          ((ModuleCat.extendScalars.{u, u, u} h₁).obj M)
          ((ModuleCat.extendScalars.{u, u, u} g₂).map
            ((canonicalUnderivedBaseChangeComparison.{u, w} f g₁ h₁ i₁ sq₁).app M) y))
      (ModuleCat.extendScalarsComp_hom_app_one_tmul g₁ g₂
        ((ModuleCat.restrictScalars.{u} f).obj M) m)).trans
    ((congrArg (fun y ↦
        (canonicalUnderivedBaseChangeComparison.{u, w} i₁ g₂ h₂ i₂ sq₂).app
          ((ModuleCat.extendScalars.{u, u, u} h₁).obj M) y)
      (congrArg (fun y ↦ (1 : R'') ⊗ₜ[R', g₂] y) h1)).trans h2)).trans
    ((congrArg (fun y ↦ (ModuleCat.extendScalarsComp.{u, u} h₁ h₂).hom.app M y) h3).trans
      (ModuleCat.extendScalarsComp_hom_app_one_tmul h₁ h₂ M m)).symm)

/-- The pasting law for the underived comparison, with the scalar-tower isomorphism of the upper
row inverted. -/
private theorem underivedPasteInv
    (f : R →+* A) (g₁ : R →+* R') (h₁ : A →+* A') (i₁ : R' →+* A')
    (g₂ : R' →+* R'') (h₂ : A' →+* A'') (i₂ : R'' →+* A'')
    (sq₁ : h₁.comp f = i₁.comp g₁) (sq₂ : h₂.comp i₁ = i₂.comp g₂)
    (sq : (h₂.comp h₁).comp f = i₂.comp (g₂.comp g₁)) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalarsComp.{u, u} g₁ g₂).hom.app
        ((ModuleCat.restrictScalars.{u} f).obj M) ≫
      (ModuleCat.extendScalars.{u, u, u} g₂).map
        ((canonicalUnderivedBaseChangeComparison.{u, w} f g₁ h₁ i₁ sq₁).app M) ≫
      (canonicalUnderivedBaseChangeComparison.{u, w} i₁ g₂ h₂ i₂ sq₂).app
        ((ModuleCat.extendScalars.{u, u, u} h₁).obj M) ≫
      (ModuleCat.restrictScalars.{u} i₂).map
        ((ModuleCat.extendScalarsComp.{u, u} h₁ h₂).inv.app M) =
    (canonicalUnderivedBaseChangeComparison.{u, w} f (g₂.comp g₁) (h₂.comp h₁) i₂ sq).app M := by
  have h := canonicalUnderivedBaseChangeComparison_paste.{u, w} f g₁ h₁ i₁ g₂ h₂ i₂ sq₁ sq₂ sq M
  simp only [← Category.assoc] at h ⊢
  rw [h, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The pasting law for the underived comparison, at a complex. -/
private theorem underivedPasteComplex
    (f : R →+* A) (g₁ : R →+* R') (h₁ : A →+* A') (i₁ : R' →+* A')
    (g₂ : R' →+* R'') (h₂ : A' →+* A'') (i₂ : R'' →+* A'')
    (sq₁ : h₁.comp f = i₁.comp g₁) (sq₂ : h₂.comp i₁ = i₂.comp g₂)
    (sq : (h₂.comp h₁).comp f = i₂.comp (g₂.comp g₁))
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} g₁ g₂)
          (ComplexShape.up ℤ)).hom.app
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      ((ModuleCat.extendScalars.{u, u, u} g₂).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (canonicalUnderivedBaseChangeComparison.{u, w} f g₁ h₁ i₁ sq₁)
          (ComplexShape.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex
          (canonicalUnderivedBaseChangeComparison.{u, w} i₁ g₂ h₂ i₂ sq₂)
          (ComplexShape.up ℤ)).app
        (((ModuleCat.extendScalars.{u, u, u} h₁).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      ((ModuleCat.restrictScalars.{u} i₂).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} h₁ h₂)
          (ComplexShape.up ℤ)).inv.app K) =
    (NatTrans.mapHomologicalComplex
      (canonicalUnderivedBaseChangeComparison.{u, w} f (g₂.comp g₁) (h₂.comp h₁) i₂ sq)
      (ComplexShape.up ℤ)).app K := by
  ext i : 1
  exact underivedPasteInv.{u, w} f g₁ h₁ i₁ g₂ h₂ i₂ sq₁ sq₂ sq (K.X i)

/-- **The diagram chase behind the pasting law.** Three functors `F`, `G`, `H` into a common
category, the equations the two floors of the pasting satisfy, and the conclusion.  Everything is
abstract: the composites occurring in the pasting law have types written partly with
`CategoryTheory.Functor.comp` and partly with the composite applied by hand, so they are not
type-correct at `implicit` transparency and the rewriting tactics will not fire on them, whereas
on abstract data they do. -/
private theorem pasteDiagram {𝒞 𝒟 ℰ ℱ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    [Category ℱ] (F : 𝒟 ⥤ 𝒞) (G : ℰ ⥤ 𝒞) (H : ℱ ⥤ 𝒞)
    {d₁ d₂ d₃ d₄ d₅ : 𝒟} {e₁ e₂ e₃ e₄ e₅ e₆ : ℰ} {b₁ b₂ b₃ b₄ b₅ : ℱ} {o₁ o₂ : 𝒞}
    (cH : d₁ ⟶ d₂) (cmp : d₂ ⟶ d₃) (aA : d₁ ⟶ d₄) (aB : d₄ ⟶ d₅) (aC : d₅ ⟶ d₃)
    (xX : e₄ ⟶ e₁) (yY : e₁ ⟶ e₂) (zZ : e₂ ⟶ e₃) (pP : e₄ ⟶ e₅) (qQ : e₅ ⟶ e₆) (rR : e₆ ⟶ e₃)
    (phig : b₁ ⟶ b₂) (psi2 : b₂ ⟶ b₃) (psi3 : b₃ ⟶ b₄) (psi4 : b₄ ⟶ b₅) (psi0 : b₁ ⟶ b₅)
    (cGi : o₁ ⟶ G.obj e₄) (s0 : G.obj e₄ ⟶ o₁)
    (t2 : G.obj e₁ ⟶ F.obj d₁) (t2' : G.obj e₂ ⟶ F.obj d₄)
    (u3 : F.obj d₃ ⟶ H.obj b₅) (w1 : F.obj d₅ ⟶ H.obj b₄)
    (dd2 : G.obj e₃ ⟶ H.obj b₃) (q1 : G.obj e₆ ⟶ H.obj b₂) (r0 : H.obj b₂ ⟶ H.obj b₁)
    (s1 : G.obj e₅ ⟶ o₂) (v1 : o₁ ⟶ o₂) (v2 : o₂ ⟶ H.obj b₁)
    (hinv : cGi ≫ s0 = 𝟙 o₁)
    (hc1 : aA ≫ aB ≫ aC = cH ≫ cmp)
    (hE2 : t2 ≫ F.map aA = G.map yY ≫ t2')
    (hE3 : F.map aC ≫ u3 = w1 ≫ H.map psi4)
    (hE4 : t2' ≫ F.map aB ≫ w1 = G.map zZ ≫ dd2 ≫ H.map psi3)
    (hc5 : xX ≫ yY ≫ zZ = pP ≫ qQ ≫ rR)
    (hE6 : G.map rR ≫ dd2 = q1 ≫ H.map psi2)
    (hc7 : G.map qQ ≫ q1 ≫ r0 = s1 ≫ v2)
    (hr : r0 ≫ H.map phig = 𝟙 (H.obj b₂))
    (hE8 : G.map pP ≫ s1 = s0 ≫ v1)
    (hc9 : phig ≫ psi2 ≫ psi3 ≫ psi4 = psi0) :
    (cGi ≫ G.map xX ≫ t2 ≫ F.map cH) ≫ F.map cmp ≫ u3 = v1 ≫ v2 ≫ H.map psi0 := by
  have hE1 : F.map cH ≫ F.map cmp = F.map aA ≫ F.map aB ≫ F.map aC := by
    simp only [← Functor.map_comp, hc1]
  have hE5 : G.map xX ≫ G.map yY ≫ G.map zZ = G.map pP ≫ G.map qQ ≫ G.map rR := by
    simp only [← Functor.map_comp, hc5]
  have hE7 : G.map qQ ≫ q1 = s1 ≫ v2 ≫ H.map phig := by
    simpa only [Category.assoc, hr, Category.comp_id] using
      congrArg (fun z ↦ z ≫ H.map phig) hc7
  have hE9 : H.map phig ≫ H.map psi2 ≫ H.map psi3 ≫ H.map psi4 = H.map psi0 := by
    simp only [← Functor.map_comp, hc9]
  simp only [Category.assoc]
  rw [reassoc_of% hE1, reassoc_of% hE2, hE3, reassoc_of% hE4, reassoc_of% hE5,
    reassoc_of% hE6, reassoc_of% hE7, reassoc_of% hE8, reassoc_of% hinv, hE9]

/-- The counit equation for the pasted transformation, at any complex. -/
private theorem pastedCounit
    (f : R →+* A) (g₁ : R →+* R') (h₁ : A →+* A') (i₁ : R' →+* A')
    (g₂ : R' →+* R'') (h₂ : A' →+* A'') (i₂ : R'' →+* A'')
    (sq₁ : h₁.comp f = i₁.comp g₁) (sq₂ : h₂.comp i₁ = i₂.comp g₂)
    (sq : (h₂.comp h₁).comp f = i₂.comp (g₂.comp g₁))
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((totalDerivedExtensionScalarsComp.{u, u} g₁ g₂).inv.app
          ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        (totalDerivedExtensionScalars.{u, u, u} g₂).functor.map
          ((canonicalBaseChangeComparison.{u, w} f g₁ h₁ i₁ sq₁).app
            (DerivedCategory.Q.obj K)) ≫
        (canonicalBaseChangeComparison.{u, w} i₁ g₂ h₂ i₂ sq₂).app
          ((totalDerivedExtensionScalars.{u, u, u} h₁).functor.obj (DerivedCategory.Q.obj K)) ≫
        (ModuleCat.restrictScalars.{u} i₂).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} h₁ h₂).hom.app (DerivedCategory.Q.obj K))) ≫
      (ModuleCat.restrictScalars.{u} i₂).mapDerivedCategory.map
        ((totalDerivedExtensionScalars.{u, u, u} (h₂.comp h₁)).comparison.app K) ≫
      (ModuleCat.restrictScalars.{u} i₂).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.extendScalars.{u, u, u} (h₂.comp h₁)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) =
    (totalDerivedExtensionScalars.{u, u, u} (g₂.comp g₁)).functor.map
        ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app K) ≫
      (totalDerivedExtensionScalars.{u, u, u} (g₂.comp g₁)).comparison.app
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (canonicalUnderivedBaseChangeComparison.{u, w} f (g₂.comp g₁) (h₂.comp h₁) i₂ sq)
        (ComplexShape.up ℤ)).app K) :=
  pasteDiagram
    (ModuleCat.restrictScalars.{u} i₂).mapDerivedCategory
    (totalDerivedExtensionScalars.{u, u, u} g₂).functor DerivedCategory.Q
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((totalDerivedExtensionScalarsComp.{u, u} g₁ g₂).inv_hom_id_app
      ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj (DerivedCategory.Q.obj K)))
    (totalDerivedExtensionScalarsComp_comparison.{u, u} h₁ h₂ K)
    ((canonicalBaseChangeComparison.{u, w} i₁ g₂ h₂ i₂ sq₂).naturality
      ((totalDerivedExtensionScalars.{u, u, u} h₁).comparison.app K)).symm
    ((ModuleCat.restrictScalars.{u} i₂).mapDerivedCategoryFactors_hom_naturality
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} h₁ h₂)
        (ComplexShape.up ℤ)).inv.app K))
    (canonicalBaseChangeComparison_counit.{u, w} i₁ g₂ h₂ i₂ sq₂
      (((ModuleCat.extendScalars.{u, u, u} h₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (canonicalBaseChangeComparison_counit.{u, w} f g₁ h₁ i₁ sq₁ K)
    ((totalDerivedExtensionScalars.{u, u, u} g₂).comparison.naturality
      ((NatTrans.mapHomologicalComplex
        (canonicalUnderivedBaseChangeComparison.{u, w} f g₁ h₁ i₁ sq₁)
        (ComplexShape.up ℤ)).app K))
    (totalDerivedExtensionScalarsComp_comparison.{u, u} g₁ g₂
      (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    ((extensionOfScalarsComplexComp.{u, u, w} g₁ g₂).inv_hom_id_app
      (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    ((totalDerivedExtensionScalarsComp.{u, u} g₁ g₂).hom.naturality
      ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app K))
    (underivedPasteComplex.{u, w} f g₁ h₁ i₁ g₂ h₂ i₂ sq₁ sq₂ sq K)

/-- The pasted transformation: the comparison of the lower square, extended along `g₂`, followed
by the comparison of the upper square, read through the composition isomorphisms of derived
extension of scalars. -/
private def pastedComparison
    (f : R →+* A) (g₁ : R →+* R') (h₁ : A →+* A') (i₁ : R' →+* A')
    (g₂ : R' →+* R'') (h₂ : A' →+* A'') (i₂ : R'' →+* A'')
    (sq₁ : h₁.comp f = i₁.comp g₁) (sq₂ : h₂.comp i₁ = i₂.comp g₂) :
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} (g₂.comp g₁)).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} (h₂.comp h₁)).functor ⋙
        (ModuleCat.restrictScalars.{u} i₂).mapDerivedCategory :=
  Functor.whiskerLeft (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
      (totalDerivedExtensionScalarsComp.{u, u} g₁ g₂).inv ≫
    Functor.whiskerRight (canonicalBaseChangeComparison.{u, w} f g₁ h₁ i₁ sq₁)
      (totalDerivedExtensionScalars.{u, u, u} g₂).functor ≫
    Functor.whiskerLeft (totalDerivedExtensionScalars.{u, u, u} h₁).functor
      (canonicalBaseChangeComparison.{u, w} i₁ g₂ h₂ i₂ sq₂) ≫
    Functor.whiskerRight (totalDerivedExtensionScalarsComp.{u, u} h₁ h₂).hom
      (ModuleCat.restrictScalars.{u} i₂).mapDerivedCategory

/-- **The pasting law of Tag 065Z.** For two commutative squares of commutative rings stacked on
top of one another, the comparison of the outer square agrees with the comparison of the lower
square, extended along the upper left map, followed by the comparison of the upper square — both
read through the composition isomorphisms of derived extension of scalars.

Both sides are determined by the same counit equation at K-flat complexes, so the identity
reduces to the underived comparison on pure tensors. -/
@[stacks 065Z "the comparison of a horizontal composite of two commutative squares of rings is \
the composite of the two comparisons, read through the composition isomorphisms of derived \
extension of scalars; this is what compatibility of the comparison with localizing a square \
amounts to"]
public theorem canonicalBaseChangeComparison_paste
    (f : R →+* A) (g₁ : R →+* R') (h₁ : A →+* A') (i₁ : R' →+* A')
    (g₂ : R' →+* R'') (h₂ : A' →+* A'') (i₂ : R'' →+* A'')
    (sq₁ : h₁.comp f = i₁.comp g₁) (sq₂ : h₂.comp i₁ = i₂.comp g₂)
    (X : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalarsComp.{u, u} g₁ g₂).hom.app
        ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj X) ≫
      (canonicalBaseChangeComparison.{u, w} f (g₂.comp g₁) (h₂.comp h₁) i₂
        (comp_comp_eq_comp_comp f g₁ h₁ i₁ g₂ h₂ i₂ sq₁ sq₂)).app X =
    (totalDerivedExtensionScalars.{u, u, u} g₂).functor.map
        ((canonicalBaseChangeComparison.{u, w} f g₁ h₁ i₁ sq₁).app X) ≫
      (canonicalBaseChangeComparison.{u, w} i₁ g₂ h₂ i₂ sq₂).app
        ((totalDerivedExtensionScalars.{u, u, u} h₁).functor.obj X) ≫
      (ModuleCat.restrictScalars.{u} i₂).mapDerivedCategory.map
        ((totalDerivedExtensionScalarsComp.{u, u} h₁ h₂).hom.app X) := by
  have heq := canonicalBaseChangeComparison_eq_of_counit.{u, w} f (g₂.comp g₁) (h₂.comp h₁) i₂
    (comp_comp_eq_comp_comp f g₁ h₁ i₁ g₂ h₂ i₂ sq₁ sq₂)
    (pastedComparison.{u, w} f g₁ h₁ i₁ g₂ h₂ i₂ sq₁ sq₂)
    (fun K _ => pastedCounit.{u, w} f g₁ h₁ i₁ g₂ h₂ i₂ sq₁ sq₂
      (comp_comp_eq_comp_comp f g₁ h₁ i₁ g₂ h₂ i₂ sq₁ sq₂) K)
  have happ := congrArg (fun α => α.app X) heq
  dsimp only [pastedComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at happ
  rw [← happ, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-! ### Localizing a square -/

omit [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')] in
/-- **The localization square of a commutative square of rings at a prime of `A'` commutes.**
For `i : R' →+* A'` and a prime `y` of `A'`, the localization of `A'` at `y` and the localization
of `R'` at the contraction of `y` fit into a commutative square with `i` and the induced map of
local rings. -/
@[ega "0 1.5.6" "special case"]
public theorem comp_algebraMap_eq_localRingHom_comp (i : R' →+* A') (y : Ideal A') [y.IsPrime] :
    (algebraMap A' (Localization.AtPrime y)).comp i =
      (Localization.localRingHom (y.comap i) y i rfl).comp
        (algebraMap R' (Localization.AtPrime (y.comap i))) :=
  RingHom.ext fun x ↦ (Localization.localRingHom_to_map _ y i rfl x).symm

/-- **Tag 065Z is compatible with localizing a square at a prime.** Pasting a commutative square
of rings with the localization square of its right-hand column at a prime `y` of `A'` composes
the two comparisons: the comparison of the square

`R → A`, `R → R'_{y ∩ R'}`, `A → A'_y`, `R'_{y ∩ R'} → A'_y`

is the comparison of the given square, extended along `R' → R'_{y ∩ R'}`, followed by the
comparison of the localization square.  This is
`RingTheory.TorIndependence.canonicalBaseChangeComparison_paste` with the localization square as
its second floor.

Note that the localization square is *not* a pushout square; Tag 065Z attaches a comparison to
every commutative square, and that is all this uses. -/
@[stacks 065Z "the comparison is compatible with localizing a square at a prime: pasting a \
square with the localization square of its right-hand column composes the two comparisons"]
public theorem canonicalBaseChangeComparison_localization
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g) (y : Ideal A') [y.IsPrime]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Localization.AtPrime (y.comap i)))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Localization.AtPrime y))]
    (X : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalarsComp.{u, u} g
          (algebraMap R' (Localization.AtPrime (y.comap i)))).hom.app
        ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj X) ≫
      (canonicalBaseChangeComparison.{u, w} f
        ((algebraMap R' (Localization.AtPrime (y.comap i))).comp g)
        ((algebraMap A' (Localization.AtPrime y)).comp h)
        (Localization.localRingHom (y.comap i) y i rfl)
        (comp_comp_eq_comp_comp f g h i (algebraMap R' (Localization.AtPrime (y.comap i)))
          (algebraMap A' (Localization.AtPrime y))
          (Localization.localRingHom (y.comap i) y i rfl) sq
          (comp_algebraMap_eq_localRingHom_comp i y))).app X =
    (totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R' (Localization.AtPrime (y.comap i)))).functor.map
        ((canonicalBaseChangeComparison.{u, w} f g h i sq).app X) ≫
      (canonicalBaseChangeComparison.{u, w} i
          (algebraMap R' (Localization.AtPrime (y.comap i)))
          (algebraMap A' (Localization.AtPrime y))
          (Localization.localRingHom (y.comap i) y i rfl)
          (comp_algebraMap_eq_localRingHom_comp i y)).app
        ((totalDerivedExtensionScalars.{u, u, u} h).functor.obj X) ≫
      (ModuleCat.restrictScalars.{u}
            (Localization.localRingHom (y.comap i) y i rfl)).mapDerivedCategory.map
        ((totalDerivedExtensionScalarsComp.{u, u} h
          (algebraMap A' (Localization.AtPrime y))).hom.app X) :=
  canonicalBaseChangeComparison_paste.{u, w} f g h i
    (algebraMap R' (Localization.AtPrime (y.comap i)))
    (algebraMap A' (Localization.AtPrime y))
    (Localization.localRingHom (y.comap i) y i rfl) sq
    (comp_algebraMap_eq_localRingHom_comp i y) X

end RingTheory.TorIndependence

end
