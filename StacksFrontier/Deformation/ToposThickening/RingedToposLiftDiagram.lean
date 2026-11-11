module

public import StacksFrontier.Deformation.ToposThickening.InverseImageKernelIdeal
public import StacksFrontier.Deformation.ToposThickening.FirstOrderLiftDiagram
import StacksCore.Tactic.StacksAttribute

/-!
# The diagram of Stacks 08UG for genuine morphisms of ringed topoi

[Stacks Project, Tag 08UG] starts from the commutative diagram (08UH) of ringed topoi

```
          (Sh(𝒞₂), 𝒪₂) --i₂--> (Sh(𝒞'₂), 𝒪'₂)
         /  |f₂                    |f'₂
        g  (Sh(ℬ₂), 𝒪_{ℬ₂}) --t₂--> (Sh(ℬ'₂), 𝒪_{ℬ'₂})
       /     |                       |
(Sh(𝒞₁), 𝒪₁) --i₁--> (Sh(𝒞'₁), 𝒪'₁)  |
   |f₁   h  ↙             |f'₁   h' ↙
(Sh(ℬ₁), 𝒪_{ℬ₁}) --t₁--> (Sh(ℬ'₁), 𝒪_{ℬ'₁})
```

whose horizontal arrows are first order thickenings, together with a `g⁻¹𝒪₁`-linear map
`ν : g⁻¹𝒢₁ ⟶ 𝒢₂` of the ideals `𝒢ⱼ = Ker(iⱼ^♯)` making the diagram of ideal rows (08UI)
commute, the front and back rows being solutions of the extension problem (08UF). The four
reduced ringed topoi and the four morphisms `f₁, f₂, g, h` are arbitrary.

As in the source ("we identify the underlying topoi for every thickening in sight (we have
already used this convention in the statement)"), each thickening is presented on the site of
its reduction: a front or back layer is a problem `Sⱼ` of
`Deformation.ToposThickening.RingedToposExtensionProblem` (the morphism `fⱼ`, the base
thickening `𝒪_{ℬ'ⱼ} ⟶ 𝒪_{ℬⱼ}` and the inverse image `fⱼ⁻¹𝒥ⱼ` of its ideal) together with a
solution `Qⱼ` (the thickening `𝒪'ⱼ ⟶ 𝒪ⱼ`, its ideal `𝒢ⱼ`, and `f'ⱼ` in the form of the structure
map `fⱼ⁻¹𝒪_{ℬ'ⱼ} ⟶ 𝒪'ⱼ`). The thickened morphism `h'` of bases is, likewise, the morphism of
ringed topoi inducing `h` on the topoi with comorphism `hB' : h⁻¹𝒪_{ℬ'₁} ⟶ 𝒪_{ℬ'₂}`.

The structure `Deformation.ToposThickening.RingedToposLiftDiagram` records that diagram. Moving
everything onto the site of `𝒞₂` by inverse image gives the one-site diagram
`RingedToposLiftDiagram.toFirstOrderLiftDiagram` of
`Deformation.ToposThickening.FirstOrderLiftDiagram` with front layer
`g⁻¹(𝒪_{ℬ'₁} → 𝒪_{ℬ₁}, 𝒪'₁ → 𝒪₁)` and back layer `(𝒪_{ℬ'₂} → 𝒪_{ℬ₂}, 𝒪'₂ → 𝒪₂)`, the bases
read through `f₁⁻¹` and `f₂⁻¹`.

## Main definitions

* `Deformation.ToposThickening.RingedToposLiftDiagram`: the diagrams (08UH) and (08UI).
* `Deformation.ToposThickening.RingedToposLiftDiagram.baseComparison`: the comparison
  `g⁻¹f₁⁻¹ ≅ (f₁ ∘ g)⁻¹ = (h ∘ f₂)⁻¹ ≅ f₂⁻¹h⁻¹` given by the commutativity `f₁ ∘ g = h ∘ f₂`.
* `Deformation.ToposThickening.RingedToposLiftDiagram.toFirstOrderLiftDiagram`: the one-site
  diagram on `𝒞₂`.

## Implementation notes

The four ringed topoi are `AlgebraicGeometry.RingedTopos.{u, u, u}`, the universes in which the
inverse image of sheaves of modules and its derived functors are available.

The commutativity of the left square of (08UI), `ν ∘ g⁻¹c₁ = c₂ ∘ (f₁⁻¹𝒥₁ → f₂⁻¹𝒥₂)`, is the
field `nu_base`. It is stated after the injection `𝒢₂ ⊂ 𝒪'₂`, on a local section `a` of
`g⁻¹f₁⁻¹𝒥₁ ⊂ g⁻¹f₁⁻¹𝒪_{ℬ'₁}`: since the rows are solutions, `g⁻¹c₁(a)` is the section `m` of
`g⁻¹𝒢₁` with image `g⁻¹f'₁(a)` in `g⁻¹𝒪'₁`, and `c₂` of the image of `a` in `f₂⁻¹𝒥₂` has image
`f'₂(h'(a))` in `𝒪'₂`. The square commutes exactly when `ν(m)` has that image.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UH](https://stacks.math.columbia.edu/tag/08UH)
* [Stacks Project, Tag 08UI](https://stacks.math.columbia.edu/tag/08UI)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor pushforwardCommRingFunctor
  commRingImageAdjunction)
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheafCompIso)
open Deformation.ToposThickening.InverseImageExtension (invImage restrictedIdeal
  invIdealOf invKernelInclOf)

universe u

namespace Deformation.ToposThickening

namespace RingedToposLiftDiagram

variable {X₁ X₂ B₁ B₂ : RingedTopos.{u, u, u}}
  [X₁.J.HasSheafCompose (forget RingCat.{u})] [X₂.J.HasSheafCompose (forget RingCat.{u})]
  [B₁.J.HasSheafCompose (forget RingCat.{u})] [B₂.J.HasSheafCompose (forget RingCat.{u})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-! ### The comparison `g⁻¹f₁⁻¹ ≅ f₂⁻¹h⁻¹` -/

section Comparison

/-- The comparison `b⁻¹a⁻¹R ≅ (a ∘ b)⁻¹R` of the iterated inverse image of a sheaf of commutative
rings with its inverse image along the composite, with the target spelled through the composite
morphism of ringed topoi. It is the identity on underlying sheaves of sets. -/
def compIso {Z Y W : RingedTopos.{u, u, u}}
    [Z.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
    [W.J.HasSheafCompose (forget RingCat.{u})]
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [W.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (a : RingedToposHom Y W) (b : RingedToposHom Z Y) (R : Sheaf W.J CommRingCat.{u}) :
    (inverseImageCommRingFunctor b.toToposHom).obj
        ((inverseImageCommRingFunctor a.toToposHom).obj R) ≅
      (inverseImageCommRingFunctor (a.comp b).toToposHom).obj R :=
  pullbackCommRingSheafCompIso Z.J Y.J b.toToposHom.inverseImage a.toToposHom.inverseImage R

section CompIso

variable {Z Y W : RingedTopos.{u, u, u}}
  [Z.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [W.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget CommRingCat.{u})]

omit [Z.J.HasSheafCompose (forget CommRingCat)] in
/-- The inverse image of a morphism of sheaves of commutative rings, on underlying sheaves of
sets. -/
theorem forgetRing_map_inverseImage (T : MorphismOfTopoi Z.Topos W.Topos)
    {R R' : Sheaf W.J CommRingCat.{u}} (r : R ⟶ R') :
    Z.forgetRing.map ((inverseImageCommRingFunctor T).map r) =
      T.inverseImage.map (W.forgetRing.map r) :=
  Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap Z.J
    T.inverseImage r

omit [Z.J.HasSheafCompose (forget CommRingCat)] in
/-- `compIso` is the identity on underlying sheaves of sets. -/
theorem forgetRing_map_compIso_hom (a : RingedToposHom Y W) (b : RingedToposHom Z Y)
    (R : Sheaf W.J CommRingCat.{u}) : Z.forgetRing.map (compIso a b R).hom = 𝟙 _ :=
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCompIso_hom_forget Z.J Y.J
    b.toToposHom.inverseImage a.toToposHom.inverseImage R

omit [Z.J.HasSheafCompose (forget CommRingCat)] in
/-- The inverse of `compIso` is the identity on underlying sheaves of sets. -/
theorem forgetRing_map_compIso_inv (a : RingedToposHom Y W) (b : RingedToposHom Z Y)
    (R : Sheaf W.J CommRingCat.{u}) : Z.forgetRing.map (compIso a b R).inv = 𝟙 _ := by
  have h2 : Z.forgetRing.map (compIso a b R).hom ≫ Z.forgetRing.map (compIso a b R).inv =
      𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [forgetRing_map_compIso_hom] at h2
  exact (Category.id_comp _).symm.trans h2

omit [Z.J.HasSheafCompose (forget CommRingCat)] in
/-- `compIso` is natural. -/
theorem compIso_hom_naturality [W.J.HasSheafCompose (forget CommRingCat.{u})]
    (a : RingedToposHom Y W) (b : RingedToposHom Z Y) {R R' : Sheaf W.J CommRingCat.{u}}
    (r : R ⟶ R') :
    (inverseImageCommRingFunctor b.toToposHom).map
        ((inverseImageCommRingFunctor a.toToposHom).map r) ≫ (compIso a b R').hom =
      (compIso a b R).hom ≫ (inverseImageCommRingFunctor (a.comp b).toToposHom).map r := by
  refine Z.forgetRing.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, forgetRing_map_compIso_hom, forgetRing_map_compIso_hom,
    forgetRing_map_inverseImage, forgetRing_map_inverseImage, forgetRing_map_inverseImage]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The structure map of `b` after `b⁻¹` of that of `a` is the structure map of `a ∘ b` after
`compIso`. -/
private theorem map_fSharpInverseImage_comp_eq (a : RingedToposHom Y W) (b : RingedToposHom Z Y) :
    (inverseImageCommRingFunctor b.toToposHom).map a.fSharpInverseImage ≫ b.fSharpInverseImage =
      (compIso a b W.O).hom ≫ (a.comp b).fSharpInverseImage := by
  rw [InverseImageExtension.comp_fSharpInverseImage_eq a b]
  exact (Iso.hom_inv_id_assoc _ _).symm

end CompIso

variable {f₁ : RingedToposHom X₁ B₁} {f₂ : RingedToposHom X₂ B₂} {g : RingedToposHom X₂ X₁}
  {h : RingedToposHom B₂ B₁} (comm : f₁.comp g = h.comp f₂) (R : Sheaf B₁.J CommRingCat.{u})

/-- The equality `(f₁ ∘ g)⁻¹R = (h ∘ f₂)⁻¹R` given by the commutative square. -/
def commIso : (inverseImageCommRingFunctor (f₁.comp g).toToposHom).obj R ≅
    (inverseImageCommRingFunctor (h.comp f₂).toToposHom).obj R :=
  eqToIso (congrArg (fun T ↦ (inverseImageCommRingFunctor T).obj R)
    (congrArg RingedToposHom.toToposHom comm))

/-- The comparison `g⁻¹f₁⁻¹R ≅ f₂⁻¹h⁻¹R` of the two iterated inverse images of a sheaf of
commutative rings on `ℬ₁` along the two sides of the commutative square `f₁ ∘ g = h ∘ f₂`: the
comparison of iterated inverse images with the inverse image along the composite, on each side,
and the equality of the two composites. It is the identity on underlying sheaves of sets. -/
def baseComparison :
    (invImage g).obj ((inverseImageCommRingFunctor f₁.toToposHom).obj R) ≅
      (inverseImageCommRingFunctor f₂.toToposHom).obj
        ((inverseImageCommRingFunctor h.toToposHom).obj R) :=
  compIso f₁ g R ≪≫ commIso comm R ≪≫ (compIso h f₂ R).symm

variable [X₂.J.HasSheafCompose (forget CommRingCat.{u})]
  [B₁.J.HasSheafCompose (forget CommRingCat.{u})]

omit [X₂.J.HasSheafCompose (forget CommRingCat)] [B₁.J.HasSheafCompose (forget CommRingCat)] in
/-- The equality `(f₁ ∘ g)⁻¹ = (h ∘ f₂)⁻¹` is natural. -/
theorem commIso_hom_naturality {R R' : Sheaf B₁.J CommRingCat.{u}} (r : R ⟶ R') :
    (inverseImageCommRingFunctor (f₁.comp g).toToposHom).map r ≫ (commIso comm R').hom =
      (commIso comm R).hom ≫ (inverseImageCommRingFunctor (h.comp f₂).toToposHom).map r := by
  have key : ∀ (T T' : MorphismOfTopoi X₂.Topos B₁.Topos) (e : T = T'),
      (inverseImageCommRingFunctor T).map r ≫
          eqToHom (congrArg (fun T ↦ (inverseImageCommRingFunctor T).obj R') e) =
        eqToHom (congrArg (fun T ↦ (inverseImageCommRingFunctor T).obj R) e) ≫
          (inverseImageCommRingFunctor T').map r := by
    rintro T _ rfl
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact key _ _ (congrArg RingedToposHom.toToposHom comm)

omit [X₂.J.HasSheafCompose (forget CommRingCat)] in
/-- The comparison `g⁻¹f₁⁻¹ ≅ f₂⁻¹h⁻¹` is natural. -/
theorem baseComparison_hom_naturality {R R' : Sheaf B₁.J CommRingCat.{u}} (r : R ⟶ R') :
    (invImage g).map ((inverseImageCommRingFunctor f₁.toToposHom).map r) ≫
        (baseComparison comm R').hom =
      (baseComparison comm R).hom ≫ (inverseImageCommRingFunctor f₂.toToposHom).map
        ((inverseImageCommRingFunctor h.toToposHom).map r) := by
  simp only [baseComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, compIso_hom_naturality, Category.assoc, ← Category.assoc _ _
    (compIso h f₂ R').inv, commIso_hom_naturality, Category.assoc]
  congr 2
  rw [Iso.comp_inv_eq, Category.assoc, compIso_hom_naturality, Iso.inv_hom_id_assoc]

end Comparison

end RingedToposLiftDiagram

section Diagram

variable (X₁ X₂ B₁ B₂ : RingedTopos.{u, u, u})
  [X₁.J.HasSheafCompose (forget RingCat.{u})] [X₂.J.HasSheafCompose (forget RingCat.{u})]
  [B₁.J.HasSheafCompose (forget RingCat.{u})] [B₂.J.HasSheafCompose (forget RingCat.{u})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₁.J.HasSheafCompose (forget CommRingCat.{u})] [X₂.J.HasSheafCompose (forget CommRingCat.{u})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X₂.J AddCommGrpCat.{u}] [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The diagram of first order thickenings of ringed topoi and the diagram (08UI) of their
ideals**, for genuine morphisms of ringed topoi.

* `S₁`, `Q₁` are the front layer: the morphism `f₁ : (Sh(𝒞₁), 𝒪₁) ⟶ (Sh(ℬ₁), 𝒪_{ℬ₁})`, the first
  order thickening `t₁` of the base, with `f₁⁻¹𝒥₁`, the ideal `𝒢₁` of `i₁`, and the front row of
  (08UI), which is a solution of (08UF) — the thickening `𝒪'₁ ⟶ 𝒪₁` with its ideal `𝒢₁` and the
  structure map `f₁⁻¹𝒪_{ℬ'₁} ⟶ 𝒪'₁` of `f'₁`.
* `S₂`, `Q₂` are the back layer, the same data with index `2`.
* `g : (Sh(𝒞₂), 𝒪₂) ⟶ (Sh(𝒞₁), 𝒪₁)` and `h : (Sh(ℬ₂), 𝒪_{ℬ₂}) ⟶ (Sh(ℬ₁), 𝒪_{ℬ₁})` are the two
  oblique arrows of the reduced part, with `f₁ ∘ g = h ∘ f₂`.
* `hB'` is the oblique arrow `h' : (Sh(ℬ'₂), 𝒪_{ℬ'₂}) ⟶ (Sh(ℬ'₁), 𝒪_{ℬ'₁})` of the thickened
  bases; the underlying topoi being identified it induces `h` on the topoi, and it is recorded by
  its comorphism `h⁻¹𝒪_{ℬ'₁} ⟶ 𝒪_{ℬ'₂}`. `hB'_reduction` is `t₁ ∘ h = h' ∘ t₂`.
* `nu` is `ν : g⁻¹𝒢₁ ⟶ 𝒢₂`, linear over `g⁻¹𝒪₁`, and `nu_base` the commutativity of the left
  square of (08UI); see the module docstring.

The faces `f'ⱼ ∘ iⱼ = tⱼ ∘ fⱼ` of (08UH) are part of the solutions `Qⱼ`. The special case
where everything lives on one site, with identity underlying topoi, is
`Deformation.ToposThickening.LiftDiagram`. -/
@[stacks 08UH "the commutative diagram of morphisms of ringed topoi, for genuine morphisms \
f₁, f₂, g, h between four arbitrary ringed topoi, each thickening presented on the site of its \
reduction as in the source's convention",
  stacks 08UI "the commutative diagram of exact ideal rows: the front and back rows are the \
solutions `Q₁`, `Q₂` of (08UF) (the exact sequences `0 → 𝒢ⱼ → 𝒪'ⱼ → 𝒪ⱼ → 0` over \
`0 → fⱼ⁻¹𝒥ⱼ → fⱼ⁻¹𝒪_{ℬ'ⱼ} → fⱼ⁻¹𝒪_{ℬⱼ} → 0` with the maps `cⱼ`), the north-north-west \
arrows are `nu` (a map of `g⁻¹𝒪₁`-modules `g⁻¹𝒢₁ → 𝒢₂`), `g^♯` and the base comparisons \
through `h` and `hB'`, and the only condition on `nu` is the source's: the left square \
`ν ∘ g⁻¹c₁ = c₂ ∘ (g⁻¹f₁⁻¹𝒥₁ → f₂⁻¹𝒥₂)` commutes (`nu_base`, stated after the injection \
`𝒢₂ ⊂ 𝒪'₂` on sections of the base ideal); the remaining squares commute by `comm`, \
`hB'_reduction` and the solutions' faces"]
structure RingedToposLiftDiagram where
  /-- The front problem: `f₁`, the base thickening `t₁` and `f₁⁻¹𝒥₁`, and the module `𝒢₁`. -/
  S₁ : RingedToposExtensionProblem X₁ B₁
  /-- The front row of (08UI): the thickening `i₁` and the structure map of `f'₁`. -/
  Q₁ : S₁.CompatibleFirstOrderThickening
  /-- The back problem: `f₂`, the base thickening `t₂` and `f₂⁻¹𝒥₂`, and the module `𝒢₂`. -/
  S₂ : RingedToposExtensionProblem X₂ B₂
  /-- The back row of (08UI): the thickening `i₂` and the structure map of `f'₂`. -/
  Q₂ : S₂.CompatibleFirstOrderThickening
  /-- The morphism `g : (Sh(𝒞₂), 𝒪₂) ⟶ (Sh(𝒞₁), 𝒪₁)`. -/
  g : RingedToposHom X₂ X₁
  /-- The morphism `(Sh(ℬ₂), 𝒪_{ℬ₂}) ⟶ (Sh(ℬ₁), 𝒪_{ℬ₁})`. -/
  h : RingedToposHom B₂ B₁
  /-- The reduced square commutes: `f₁ ∘ g = h ∘ f₂`. -/
  comm : S₁.f.comp g = h.comp S₂.f
  /-- The comorphism `h⁻¹𝒪_{ℬ'₁} ⟶ 𝒪_{ℬ'₂}` of the thickened morphism of bases `h'`. -/
  hB' : (inverseImageCommRingFunctor h.toToposHom).obj S₁.baseExtension ⟶ S₂.baseExtension
  /-- The square of bases commutes: `t₁ ∘ h = h' ∘ t₂`. -/
  hB'_reduction : hB' ≫ S₂.baseReduction =
    (inverseImageCommRingFunctor h.toToposHom).map S₁.baseReduction ≫ h.fSharpInverseImage
  /-- `ν : g⁻¹𝒢₁ ⟶ 𝒢₂`, a map of `g⁻¹𝒪₁`-modules. -/
  nu : invIdealOf g S₁.G ⟶ (SheafOfModules.restrictScalars
    ((sheafCompose X₂.J (forget₂ CommRingCat.{u} RingCat.{u})).map g.fSharpInverseImage)).obj S₂.G
  /-- The left square of (08UI) commutes: for a local section `a` of `g⁻¹f₁⁻¹𝒥₁`, whose image
  `g⁻¹f'₁(a)` in `g⁻¹𝒪'₁` is the image of the section `m = g⁻¹c₁(a)` of `g⁻¹𝒢₁`, the image
  `f'₂(h'(a))` of `a` in `𝒪'₂` is the image of `ν(m)`. -/
  nu_base : ∀ (U : X₂.Cᵒᵖ)
    (a : ((invImage g).obj
      ((inverseImageCommRingFunctor S₁.f.toToposHom).obj S₁.baseExtension)).obj.obj U)
    (m : (invIdealOf g S₁.G).val.obj U),
    ((invImage g).map ((inverseImageCommRingFunctor S₁.f.toToposHom).map
      S₁.baseReduction)).hom.app U a = 0 →
    ((invImage g).map Q₁.baseMap).hom.app U a =
      (show ((invImage g).obj Q₁.extension).obj.obj U from
        (invKernelInclOf Q₁.reduction Q₁.kernelInclusion g).val.app U m) →
    Q₂.baseMap.hom.app U
        (((RingedToposLiftDiagram.baseComparison comm S₁.baseExtension).hom ≫
          (inverseImageCommRingFunctor S₂.f.toToposHom).map hB').hom.app U a) =
      (show Q₂.extension.obj.obj U from
        Q₂.kernelInclusion.val.app U (show S₂.G.val.obj U from nu.val.app U m))

end Diagram

namespace RingedToposLiftDiagram

open InverseImageExtension

variable {X₁ X₂ B₁ B₂ : RingedTopos.{u, u, u}}
  [X₁.J.HasSheafCompose (forget RingCat.{u})] [X₂.J.HasSheafCompose (forget RingCat.{u})]
  [B₁.J.HasSheafCompose (forget RingCat.{u})] [B₂.J.HasSheafCompose (forget RingCat.{u})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₁.J.HasSheafCompose (forget CommRingCat.{u})] [X₂.J.HasSheafCompose (forget CommRingCat.{u})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X₂.J AddCommGrpCat.{u}] [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (D : RingedToposLiftDiagram X₁ X₂ B₁ B₂)

/-- The inclusion `g⁻¹𝒢₁ ⟶ g⁻¹𝒪'₁` of the ideal of the front thickening moved to `𝒞₂`. -/
abbrev frontKernelIncl :=
  invKernelInclOf D.Q₁.reduction D.Q₁.kernelInclusion D.g

/-- The inclusion `g⁻¹f₁⁻¹𝒥₁ ⟶ g⁻¹f₁⁻¹𝒪_{ℬ'₁}` of the ideal of the front base thickening moved
to `𝒞₂`. -/
abbrev frontBaseIdealIncl :=
  invKernelInclOf ((inverseImageCommRingFunctor D.S₁.f.toToposHom).map D.S₁.baseReduction)
    D.S₁.idealInclusion D.g

/-- **The front layer moved to `𝒞₂`**: the inverse image along `g` of the base thickening
`f₁⁻¹𝒪_{ℬ'₁} ⟶ f₁⁻¹𝒪_{ℬ₁}`, of the thickening `𝒪'₁ ⟶ 𝒪₁`, and of the structure maps. Its ideal
is `g⁻¹𝒢₁`. -/
def frontSquare : LiftSquare X₂.J where
  OB := (invImage D.g).obj ((inverseImageCommRingFunctor D.S₁.f.toToposHom).obj B₁.O)
  OB' := (invImage D.g).obj ((inverseImageCommRingFunctor D.S₁.f.toToposHom).obj
    D.S₁.baseExtension)
  O := (invImage D.g).obj X₁.O
  O' := (invImage D.g).obj D.Q₁.extension
  baseReduction := (invImage D.g).map
    ((inverseImageCommRingFunctor D.S₁.f.toToposHom).map D.S₁.baseReduction)
  reduction := (invImage D.g).map D.Q₁.reduction
  f := (invImage D.g).map D.S₁.f.fSharpInverseImage
  f' := (invImage D.g).map D.Q₁.baseMap
  comm := by rw [← Functor.map_comp, ← Functor.map_comp, D.Q₁.baseMap_reduction]
  baseLocallySurjective := isLocallySurjective_invImage_map D.g _
    (isLocallySurjective_invImage_map D.S₁.f _ D.S₁.baseLocallySurjective)
  baseSquareZero := sq_ker_eq_bot_of_kernelIncl ((invImage D.g).map
      ((inverseImageCommRingFunctor D.S₁.f.toToposHom).map D.S₁.baseReduction))
    (frontBaseIdealIncl D)
    (invKernelInclOf_mem D.S₁.idealZero D.S₁.idealUniversal D.g)
    (existsUnique_invKernelInclOf D.S₁.idealZero D.S₁.idealUniversal D.g)
  locallySurjective := isLocallySurjective_invImage_map D.g _ D.Q₁.locallySurjective
  squareZero := sq_ker_eq_bot_of_kernelIncl ((invImage D.g).map D.Q₁.reduction)
    (frontKernelIncl D)
    (invKernelInclOf_mem D.Q₁.kernelZero D.Q₁.kernelUniversal D.g)
    (existsUnique_invKernelInclOf D.Q₁.kernelZero D.Q₁.kernelUniversal D.g)
  G := invIdealOf D.g D.S₁.G
  kernelInclusion := frontKernelIncl D
  kernelZero := invKernelInclOf_mem D.Q₁.kernelZero D.Q₁.kernelUniversal D.g
  kernelUniversal := existsUnique_invKernelInclOf D.Q₁.kernelZero D.Q₁.kernelUniversal D.g

/-- **The back layer**, on its own site `𝒞₂`: the base thickening `f₂⁻¹𝒪_{ℬ'₂} ⟶ f₂⁻¹𝒪_{ℬ₂}`,
the thickening `𝒪'₂ ⟶ 𝒪₂` and the structure maps. -/
def backSquare : LiftSquare X₂.J where
  OB := (inverseImageCommRingFunctor D.S₂.f.toToposHom).obj B₂.O
  OB' := (inverseImageCommRingFunctor D.S₂.f.toToposHom).obj D.S₂.baseExtension
  O := X₂.O
  O' := D.Q₂.extension
  baseReduction := (inverseImageCommRingFunctor D.S₂.f.toToposHom).map D.S₂.baseReduction
  reduction := D.Q₂.reduction
  f := D.S₂.f.fSharpInverseImage
  f' := D.Q₂.baseMap
  comm := D.Q₂.baseMap_reduction
  baseLocallySurjective := isLocallySurjective_invImage_map D.S₂.f _ D.S₂.baseLocallySurjective
  baseSquareZero := sq_ker_eq_bot_of_kernelIncl
    ((inverseImageCommRingFunctor D.S₂.f.toToposHom).map D.S₂.baseReduction)
    D.S₂.idealInclusion D.S₂.idealZero D.S₂.idealUniversal
  locallySurjective := D.Q₂.locallySurjective
  squareZero := D.Q₂.squareZero
  G := D.S₂.G
  kernelInclusion := D.Q₂.kernelInclusion
  kernelZero := D.Q₂.kernelZero
  kernelUniversal := D.Q₂.kernelUniversal

/-- The comparison `g⁻¹f₁⁻¹𝒪_{ℬ₁} ⟶ f₂⁻¹𝒪_{ℬ₂}` of the reduced bases: `g⁻¹f₁⁻¹ ≅ f₂⁻¹h⁻¹`
followed by `f₂⁻¹` of the structure map of `h`. -/
def baseHom : (frontSquare D).OB ⟶ (backSquare D).OB :=
  (baseComparison D.comm B₁.O).hom ≫
    (inverseImageCommRingFunctor D.S₂.f.toToposHom).map D.h.fSharpInverseImage

/-- The comparison `g⁻¹f₁⁻¹𝒪_{ℬ'₁} ⟶ f₂⁻¹𝒪_{ℬ'₂}` of the thickened bases: `g⁻¹f₁⁻¹ ≅ f₂⁻¹h⁻¹`
followed by `f₂⁻¹` of the comorphism of `h'`. -/
def thickBaseHom : (frontSquare D).OB' ⟶ (backSquare D).OB' :=
  (baseComparison D.comm D.S₁.baseExtension).hom ≫
    (inverseImageCommRingFunctor D.S₂.f.toToposHom).map D.hB'

variable [B₁.J.HasSheafCompose (forget CommRingCat.{u})]

omit [X₁.J.HasSheafCompose (forget CommRingCat.{u})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X₂.J AddCommGrpCat.{u}] [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [X₂.J.HasSheafCompose (forget CommRingCat)] [B₁.J.HasSheafCompose (forget CommRingCat)] in
/-- The structure maps of the two composites `f₁ ∘ g = h ∘ f₂` agree through `commIso`. -/
theorem fSharpInverseImage_comp_eq {f₁ : RingedToposHom X₁ B₁} {f₂ : RingedToposHom X₂ B₂}
    {g : RingedToposHom X₂ X₁} {h : RingedToposHom B₂ B₁} (comm : f₁.comp g = h.comp f₂) :
    (f₁.comp g).fSharpInverseImage =
      (commIso comm B₁.O).hom ≫ (h.comp f₂).fSharpInverseImage := by
  have key : ∀ (a b : RingedToposHom X₂ B₁) (e : a = b), a.fSharpInverseImage =
      eqToHom (congrArg (fun T ↦ (inverseImageCommRingFunctor T).obj B₁.O)
        (congrArg RingedToposHom.toToposHom e)) ≫ b.fSharpInverseImage := by
    rintro a _ rfl
    simp only [eqToHom_refl, Category.id_comp]
  exact key _ _ comm

omit [HasWeakSheafify X₂.J AddCommGrpCat] [X₂.J.WEqualsLocallyBijective AddCommGrpCat]
  [B₁.J.HasSheafCompose (forget CommRingCat)] in
/-- The comparison of reduced bases lies under `g^♯`. -/
theorem baseHom_comp :
    baseHom D ≫ (backSquare D).f = (frontSquare D).f ≫ D.g.fSharpInverseImage := by
  change (baseComparison D.comm B₁.O).hom ≫
      (inverseImageCommRingFunctor D.S₂.f.toToposHom).map D.h.fSharpInverseImage ≫
        D.S₂.f.fSharpInverseImage =
    (invImage D.g).map D.S₁.f.fSharpInverseImage ≫ D.g.fSharpInverseImage
  rw [map_fSharpInverseImage_comp_eq D.S₁.f D.g, map_fSharpInverseImage_comp_eq D.h D.S₂.f,
    fSharpInverseImage_comp_eq D.comm]
  simp only [baseComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

omit [HasWeakSheafify X₂.J AddCommGrpCat] [X₂.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The comparison of thickened bases lies over the comparison of reduced bases. -/
theorem thickBaseHom_comp :
    thickBaseHom D ≫ (backSquare D).baseReduction = (frontSquare D).baseReduction ≫ baseHom D := by
  change ((baseComparison D.comm D.S₁.baseExtension).hom ≫
      (inverseImageCommRingFunctor D.S₂.f.toToposHom).map D.hB') ≫
        (inverseImageCommRingFunctor D.S₂.f.toToposHom).map D.S₂.baseReduction =
    (invImage D.g).map ((inverseImageCommRingFunctor D.S₁.f.toToposHom).map
      D.S₁.baseReduction) ≫ (baseComparison D.comm B₁.O).hom ≫
        (inverseImageCommRingFunctor D.S₂.f.toToposHom).map D.h.fSharpInverseImage
  rw [Category.assoc, ← Functor.map_comp, D.hB'_reduction, Functor.map_comp,
    ← Category.assoc, ← Category.assoc, baseComparison_hom_naturality]

/-- **The one-site diagram on `𝒞₂`**: the diagram (08UI) on the site of `𝒞₂`,
with front layer the inverse image along `g` of the front layer, back layer the back layer, and
comparisons `g^♯`, `g⁻¹f₁⁻¹ ≅ f₂⁻¹h⁻¹` followed by `h^♯`, and the same followed by `h'`. -/
def toFirstOrderLiftDiagram : FirstOrderLiftDiagram.{u, u, u} X₂.J where
  front := frontSquare D
  back := backSquare D
  g := D.g.fSharpInverseImage
  gB := baseHom D
  gB' := thickBaseHom D
  g_comm := baseHom_comp D
  gB_comm := thickBaseHom_comp D
  nu := D.nu
  nu_base := D.nu_base

end RingedToposLiftDiagram

end Deformation.ToposThickening

end
