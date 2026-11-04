module

public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Picard
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UnitTorsorsOfInvertibleModules
import StacksCore.Tactic.StacksAttribute

/-!
# First cohomology of the units and the Picard group of a locally ringed site

Let `(C, O)` be a locally ringed site. Sending an invertible `O`-module to the torsor of its
local generators is a bijection from the Picard group of `O` onto the isomorphism classes of
torsors under the sheaf of units `O^*`, and it is additive because the tensor product of two
local generators is a local generator of the tensor product. Composing with the classification
of torsors by first cohomology gives the canonical isomorphism of abelian groups
`H^1(C, O^*) = Pic(O)`.

## Main definitions

* `Stacks.Cohomology.Torsors.Generators.picardToTorsorClasses`: the generator-torsor class of a
  Picard class.
* `Stacks.Cohomology.Torsors.Generators.picardToH1Hom`: the resulting homomorphism to first
  cohomology.
* `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup`: the canonical isomorphism
  `H^1(C, O^*) ≅ Pic(O)`.

## Main results

* `Stacks.Cohomology.Torsors.Generators.picardToTorsorClasses_surjective`: every torsor under the
  units is the generator torsor of an invertible module.
* `Stacks.Cohomology.Torsors.Generators.picardToH1_add`: the map is additive.
* `Stacks.Cohomology.Torsors.Generators.picardToH1_eq_zero`: it has trivial kernel, because a
  global section of the generator torsor is a trivialization of the module.
* `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf`: the inverse
  isomorphism sends the class of an invertible module to the first cohomology class of its
  generator torsor, which fixes the correspondence rather than only its existence.

## Implementation notes

The Picard group used is `Stacks.SheafOfModules.Picard.PicardGroup`, the small model of the
skeleton of the category of invertible modules carrying Tag 040C; a Picard class is sent to the
generator-torsor class of the chosen representative of its skeleton class, and
`picardToTorsorClasses_classOf` says this agrees with the generator torsor of any representative.

Additivity is proved by exhibiting, for two invertible modules, an equivariant map from the
product of their generator torsors to the generator torsor of their tensor product; that the
tensor product of two local generators is again one is checked by comparing the multiplication
map on the slice site with the multiplication maps of the two factors, which is where local
bijectivity of the sheafification map of the tensor presheaf is used. The resulting addition
formula for torsor classes is `torsorClass_add_of_equivariant`, deduced from naturality of the
classification of Tag 03AJ in the coefficient sheaf applied to the sum of the two projections.

Triviality of the kernel is Tag 03AI: a class in the kernel has a trivial generator torsor, and a
global section of the trivial torsor gives a compatible family of local generators, that is, a
section of the module by which multiplication is an isomorphism over every object.

The tensor product of local generators is split into a universe-general part and a part that is
not.  `Stacks.Cohomology.Torsors.Generators.tensorSheafOfModules`,
`Stacks.Cohomology.Torsors.Generators.tensorSection` and
`Stacks.Cohomology.Torsors.Generators.tensorSection_restrict` are stated over a ringed site whose
objects and morphisms live in universes unrelated to the universe of its structure rings, which
is what the small étale ringed site of an algebraic space,
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, needs; the rest of the file, including
`Stacks.Cohomology.Torsors.Generators.tensorSection_bijective`, is over
`AlgebraicGeometry.RingedSite.{u, u, u}`.

Reading `tensorSection_bijective` over `AlgebraicGeometry.RingedSite.{u + 1, u, u}` is not a
matter of universe arguments: its proof descends through `Sheaf (X.J.over U) (Type u)`, and the
type-valued sheaf condition in the module universe forces that universe to dominate the site's
own.  Carrying the descent in `AddCommGrpCat.{u}` instead would avoid the constraint -- the
comparison `k` is additive in the scalar, so it is a morphism of presheaves of abelian groups
over the slice, and `R` can be taken through `forget₂ CommRingCat AddCommGrpCat` -- but it then
needs `HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}` and
`(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}` on every slice, which this project
carries as hypotheses rather than deriving, and which the small étale site has only for `X.J`
itself.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 03AI](https://stacks.math.columbia.edu/tag/03AI)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 040C](https://stacks.math.columbia.edu/tag/040C)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory

universe u v w u'

namespace Stacks.Cohomology.Torsors.Generators

/-! ### From Picard classes to torsor classes -/

/-- The abelian group structure on the Picard group of a ringed site, named here because
instance search does not find it through the universe constraints of a ringed site.

Not `local`: every consumer of `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup`
has to write down the Picard group of a ringed site, and so needs this bridge too. -/
@[sga "6 X 5.1"]
instance picardGroupAddCommGroup (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2

/-- The generator-torsor class of a Picard class: the class of the generator torsor of the
chosen representative of the corresponding isomorphism class of invertible modules. -/
def picardToTorsorClasses (X : RingedSite.{u, u, u})
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify X.J AddCommGrpCat.{u}] :
    Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 →
      Stacks.Cohomology.Torsors.torsorIsoClasses (unitsAddSheaf X) :=
  fun p => Quotient.lift
    (fun L : Stacks.SheafOfModules.InvertibleModules X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 =>
      Quotient.mk _ (generatorTorsor X hX L.obj L.property).torsor)
    (by
      intro L N h
      obtain ⟨e⟩ := h
      exact Quotient.sound (generatorTorsor_isIsomorphic_of_iso X
        ((ObjectProperty.ι _).mapIso e)
        (generatorTorsor X hX L.obj L.property)
        (generatorTorsor X hX N.obj N.property)))
    ((Stacks.SheafOfModules.Picard.picardGroupData X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2).classEquiv.symm p)

/-- On the class of an invertible module the map is the class of its generator torsor. -/
theorem picardToTorsorClasses_classOf (X : RingedSite.{u, u, u})
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L) :
    picardToTorsorClasses X hX
        (Stacks.SheafOfModules.Picard.classOf X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL) =
      Quotient.mk _ (generatorTorsor X hX L hL).torsor := by
  simp only [picardToTorsorClasses, Stacks.SheafOfModules.Picard.classOf,
    Equiv.symm_apply_apply]
  rfl

/-- **Every torsor comes from an invertible module.** -/
theorem picardToTorsorClasses_surjective (X : RingedSite.{u, u, u})
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify X.J AddCommGrpCat.{u}] :
    Function.Surjective (picardToTorsorClasses X hX) := by
  intro c
  induction c using Quotient.inductionOn with
  | h F =>
    refine ⟨Stacks.SheafOfModules.Picard.classOf X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (coefficientSheaf X F)
      (coefficientSheaf_isInvertible X F), ?_⟩
    rw [picardToTorsorClasses_classOf]
    exact Quotient.sound ((Stacks.Cohomology.Torsors.torsorSetoid (unitsAddSheaf X)).symm
      (coefficientGeneratorTorsor_isIsomorphic X hX F))

/-- Every Picard class is the class of an invertible module. -/
theorem picardGroup_exists_classOf (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (p : Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2) :
    ∃ (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L),
      Stacks.SheafOfModules.Picard.classOf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL = p :=
  Stacks.SheafOfModules.Picard.exists_classOf_eq X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 p

/-! ### Products of torsors and additivity of the classification -/

/-- The product of two presheaves of sets. -/
def productPresheaf {D : Type u} [Category.{v} D] (F G : Dᵒᵖ ⥤ Type u) : Dᵒᵖ ⥤ Type u where
  obj U := F.obj U × G.obj U
  map f := ↾(fun s => (F.map f s.1, G.map f s.2))
  map_id U := by ext s <;> simp
  map_comp f g := by ext s <;> simp

/-- The product of two sheaves of sets is a sheaf. -/
theorem productPresheaf_isSheaf {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology D) {F G : Dᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf J F) (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J (productPresheaf F G) := by
  apply (isSheaf_iff_isSheaf_of_type J _).2
  intro U S hS x hx
  let xF : Presieve.FamilyOfElements F S.arrows := fun V f hf => (x f hf).1
  let xG : Presieve.FamilyOfElements G S.arrows := fun V f hf => (x f hf).2
  have hxF : xF.Compatible := fun V W T a b f g hf hg h =>
    congrArg Prod.fst (hx a b hf hg h)
  have hxG : xG.Compatible := fun V W T a b f g hf hg h =>
    congrArg Prod.snd (hx a b hf hg h)
  obtain ⟨f, hf, hf'⟩ := hF.isSheafFor S hS xF hxF
  obtain ⟨g, hg, hg'⟩ := hG.isSheafFor S hS xG hxG
  exact ⟨(f, g), fun V a ha => Prod.ext (hf a ha) (hg a ha), fun y hy =>
    Prod.ext (hf' _ fun V a ha => congrArg Prod.fst (hy a ha))
      (hg' _ fun V a ha => congrArg Prod.snd (hy a ha))⟩

/-- The product of two abelian sheaves. -/
def productAbelianSheaf {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology D} (H K : Sheaf J AddCommGrpCat.{u}) :
    Sheaf J AddCommGrpCat.{u} := by
  let P : Dᵒᵖ ⥤ AddCommGrpCat.{u} := {
    obj := fun U => AddCommGrpCat.of (H.obj.obj U × K.obj.obj U)
    map := fun f => AddCommGrpCat.ofHom ((H.obj.map f).hom.prodMap (K.obj.map f).hom)
    map_id := by
      intro U
      apply ConcreteCategory.hom_ext
      intro x
      change ((H.obj.map (𝟙 U)) x.1, (K.obj.map (𝟙 U)) x.2) = (x.1, x.2)
      simp only [H.obj.map_id, K.obj.map_id, ConcreteCategory.id_apply]
    map_comp := by
      intro U V W f g
      apply ConcreteCategory.hom_ext
      intro x
      change ((H.obj.map (f ≫ g)) x.1, (K.obj.map (f ≫ g)) x.2) =
        ((H.obj.map g) ((H.obj.map f) x.1), (K.obj.map g) ((K.obj.map f) x.2))
      simp only [H.obj.map_comp, K.obj.map_comp, ConcreteCategory.comp_apply] }
  refine ⟨P, (Presheaf.isSheaf_iff_isSheaf_comp J P (forget AddCommGrpCat.{u})).2 ?_⟩
  exact productPresheaf_isSheaf J
    (Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat.{u}) H.property)
    (Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat.{u}) K.property)

/-- The first projection out of a product of abelian sheaves. -/
def productAbelianSheafFst {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology D} (H K : Sheaf J AddCommGrpCat.{u}) :
    productAbelianSheaf H K ⟶ H where
  hom.app _ := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
  hom.naturality _ _ _ := rfl

/-- The second projection out of a product of abelian sheaves. -/
def productAbelianSheafSnd {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology D} (H K : Sheaf J AddCommGrpCat.{u}) :
    productAbelianSheaf H K ⟶ K where
  hom.app _ := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
  hom.naturality _ _ _ := rfl

/-- The product of two torsors, a torsor under the product of the two coefficient sheaves. -/
def productAbelianTorsor {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology D} {H K : Sheaf J AddCommGrpCat.{u}}
    (F : Stacks.Cohomology.Torsors.AbelianTorsor H)
    (G : Stacks.Cohomology.Torsors.AbelianTorsor K) :
    Stacks.Cohomology.Torsors.AbelianTorsor (productAbelianSheaf H K) := by
  let P : PseudoTorsor
      (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf (productAbelianSheaf H K)) := {
    presheaf := productPresheaf F.1.presheaf G.1.presheaf
    isSheaf := productPresheaf_isSheaf J F.1.isSheaf G.1.isSheaf
    act := fun U a s =>
      (F.1.act U (Multiplicative.ofAdd (Multiplicative.toAdd a).1) s.1,
       G.1.act U (Multiplicative.ofAdd (Multiplicative.toAdd a).2) s.2)
    one_act := fun U s => Prod.ext (F.1.one_act U s.1) (G.1.one_act U s.2)
    mul_act := fun U a b s => Prod.ext (F.1.mul_act U _ _ s.1) (G.1.mul_act U _ _ s.2)
    naturality := fun f a s => Prod.ext (F.1.naturality f _ _) (G.1.naturality f _ _)
    simplyTransitive := by
      intro U h s t
      obtain ⟨a, ha, hau⟩ := F.1.simplyTransitive U ⟨s.1⟩ s.1 t.1
      obtain ⟨b, hb, hbu⟩ := G.1.simplyTransitive U ⟨s.2⟩ s.2 t.2
      refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd a, Multiplicative.toAdd b),
        Prod.ext ha hb, ?_⟩
      intro c hc
      apply congrArg Multiplicative.ofAdd
      exact Prod.ext (congrArg Multiplicative.toAdd (hau _ (congrArg Prod.fst hc)))
        (congrArg Multiplicative.toAdd (hbu _ (congrArg Prod.snd hc))) }
  refine ⟨P, ?_⟩
  intro U
  obtain ⟨S, hS, hs⟩ := F.2 U
  obtain ⟨T, hT, ht⟩ := G.2 U
  refine ⟨S ⊓ T, J.intersection_covering hS hT, ?_⟩
  intro V f hf
  obtain ⟨s⟩ := hs hf.1
  obtain ⟨t⟩ := ht hf.2
  exact ⟨(s, t)⟩

/-- **Addition of torsor classes.** If an equivariant map from the product of two torsors to a
third one adds the acting sections, then the class of the third is the sum of the two classes. -/
theorem torsorClass_add_of_equivariant {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology D} [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{u})] (H : Sheaf J AddCommGrpCat.{u})
    (F G T : Stacks.Cohomology.Torsors.AbelianTorsor H)
    (f : productPresheaf F.1.presheaf G.1.presheaf ⟶ T.1.presheaf)
    (hf : ∀ (U : Dᵒᵖ) (a b : H.obj.obj U) (s : F.1.presheaf.obj U) (t : G.1.presheaf.obj U),
      f.app U (F.1.act U (Multiplicative.ofAdd a) s,
        G.1.act U (Multiplicative.ofAdd b) t) =
      T.1.act U (Multiplicative.ofAdd (a + b)) (f.app U (s, t))) :
    Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H (Quotient.mk _ F) +
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H (Quotient.mk _ G) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H (Quotient.mk _ T) := by
  let P := productAbelianTorsor F G
  let p := productAbelianSheafFst H H
  let q := productAbelianSheafSnd H H
  let fp : P.1.presheaf ⟶ F.1.presheaf :=
    { app := fun _ => ↾Prod.fst, naturality := by intros; rfl }
  let fq : P.1.presheaf ⟶ G.1.presheaf :=
    { app := fun _ => ↾Prod.snd, naturality := by intros; rfl }
  have hp := Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_naturality p P F fp
    (by intros; rfl)
  have hq := Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_naturality q P G fq
    (by intros; rfl)
  rw [← hp, ← hq, ← Sheaf.H.map_add_apply]
  exact Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_naturality (p + q) P T f
    (fun U a s => hf U a.1 a.2 s.1 s.2)

/-! ### Tensor products of local generators -/

/-- Multiplication by the tensor product of two sections by which multiplication is bijective
is bijective. -/
theorem tensor_smul_bijective {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (s : M) (t : N) (hs : Function.Bijective (fun r : R => r • s))
    (ht : Function.Bijective (fun r : R => r • t)) :
    Function.Bijective (fun r : R => r • (s ⊗ₜ[R] t)) := by
  let e := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M s) hs
  let f := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R N t) ht
  let g : R ≃ₗ[R] TensorProduct R M N :=
    (TensorProduct.lid R R).symm.trans (TensorProduct.congr e f)
  have hg : (fun r : R => r • (s ⊗ₜ[R] t)) = g := by
    funext r
    have h1 : g r = e (1 : R) ⊗ₜ[R] f r := by simp [g]
    have h2 : e (1 : R) = s := by
      show LinearMap.toSpanSingleton R M s (1 : R) = s
      rw [LinearMap.toSpanSingleton_apply, one_smul]
    have h3 : f r = r • t := by
      show LinearMap.toSpanSingleton R N t r = r • t
      rw [LinearMap.toSpanSingleton_apply]
    rw [h1, h2, h3, TensorProduct.tmul_smul]
  rw [hg]
  exact g.bijective

section Tensor

variable (X : RingedSite.{u', v, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify X.J AddCommGrpCat.{u}]

/-- The tensor product sheaf of two sheaves of modules on a ringed site, as a sheaf of modules
over the structure sheaf of that ringed site. -/
abbrev tensorSheafOfModules
    (L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.O.obj, Presheaf.isSheaf_of_isSheaf_comp _
    (X.O.obj) (forget₂ CommRingCat RingCat)
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).2)⟩).obj (L)).obj (N))

/-- The image in the tensor product sheaf of the tensor product of two sections. -/
abbrev tensorSection (L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    (tensorSheafOfModules X L N).val.obj (op U) :=
  ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
    ((PresheafOfModules.tensorObj (O := X.O.obj) (L.val) (N.val)))).app
      (op U)).hom (s ⊗ₜ t)

/-- The tensor product of two sections is compatible with restriction. -/
theorem tensorSection_restrict
    (L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.C} (f : V ⟶ U) (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    (tensorSheafOfModules X L N).val.restrictₛₗ f.op (tensorSection X L N U s t) =
      tensorSection X L N V (L.val.restrictₛₗ f.op s) (N.val.restrictₛₗ f.op t) :=
  (PresheafOfModules.naturality_apply
    (Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      ((PresheafOfModules.tensorObj (O := X.O.obj) (L.val) (N.val))))
        f.op (s ⊗ₜ t)).symm

end Tensor

variable (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify X.J AddCommGrpCat.{u}]

/-- **Multiplication by the tensor product of two local generators is bijective.**  On the slice
site over `U` the multiplication map is the sheafification of an isomorphism: by
`Stacks.Cohomology.Torsors.Generators.tensor_smul_bijective` it is an isomorphism of presheaves
before sheafification, and the sheafification map of the tensor presheaf is locally bijective.

The two hypotheses are the local-generator property of
`Stacks.Cohomology.Torsors.Generators.GeneratorSections` written out rather than bundled, so
that the *statement* no longer mentions a notion declared only over
`AlgebraicGeometry.RingedSite.{u, u, u}`.  The declaration is still over that ringed site, and
the obstruction is now the proof alone: it descends the presheaf isomorphism along the sheaf
condition for **type-valued** presheaves in the module universe, through
`Sheaf (X.J.over U) (Type u)`, which forces `u ≥ max u' v` for a site with objects in `Type u'`
and morphisms in `Type v`.  The three declarations above carry no such constraint; see the
implementation notes of this file for what reading this one on
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` -- the small étale ringed site of an algebraic
space -- would take. -/
theorem tensorSection_bijective
    (L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : L.val.obj (op U)) (t : N.val.obj (op U))
    (hs : ∀ (V : X.C) (f : V ⟶ U),
      Function.Bijective fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ f.op s)
    (ht : ∀ (V : X.C) (f : V ⟶ U),
      Function.Bijective fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • N.val.restrictₛₗ f.op t) :
    Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) =>
      r • tensorSection X L N U s t) := by
  let instL (V : X.C) : Module (X.O.obj.obj (op V)) (L.val.obj (op V)) :=
    (L.val.obj (op V)).isModule
  let instN (V : X.C) : Module (X.O.obj.obj (op V)) (N.val.obj (op V)) :=
    (N.val.obj (op V)).isModule
  let P := (PresheafOfModules.tensorObj (O := X.O.obj) (L.val) (N.val))
  let Q := tensorSheafOfModules X L N
  let η := (PresheafOfModules.toPresheaf _).map
    (Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 P)
  let η' := Functor.whiskerRight η (forget AddCommGrpCat)
  have : Presheaf.IsLocallyInjective X.J η := by
    show Presheaf.IsLocallyInjective X.J (CategoryTheory.toSheafify X.J P.presheaf)
    infer_instance
  have : Presheaf.IsLocallySurjective X.J η := by
    show Presheaf.IsLocallySurjective X.J (CategoryTheory.toSheafify X.J P.presheaf)
    infer_instance
  let R := (X.O.over U).obj ⋙ forget CommRingCat
  let T := (Over.forget U).op ⋙ P.presheaf ⋙ forget AddCommGrpCat
  let kf (V : (Over U)ᵒᵖ) : R.obj V → T.obj V := fun r : X.O.obj.obj (op V.unop.left) =>
    r • (L.val.restrictₛₗ V.unop.hom.op s ⊗ₜ[X.O.obj.obj (op V.unop.left)]
      N.val.restrictₛₗ V.unop.hom.op t)
  have hres (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (m : M.val.obj (op U)) :
      M.val.restrictₛₗ f.unop.left.op (M.val.restrictₛₗ V.unop.hom.op m) =
        M.val.restrictₛₗ W.unop.hom.op m := by
    show M.val.map f.unop.left.op (M.val.map V.unop.hom.op m) = M.val.map W.unop.hom.op m
    rw [← M.val.map_comp_apply, ← op_comp, Over.w f.unop]
  have hknat {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (r : R.obj V) :
      kf W (R.map f r) = T.map f (kf V r) := by
    let : Module (X.O.obj.obj (op W.unop.left)) (P.obj (op W.unop.left)) :=
      (P.obj (op W.unop.left)).isModule
    have hsm := (P.restrictₛₗ f.unop.left.op).map_smulₛₗ
      (r : X.O.obj.obj (op V.unop.left))
      (L.val.restrictₛₗ V.unop.hom.op s ⊗ₜ[X.O.obj.obj (op V.unop.left)]
        N.val.restrictₛₗ V.unop.hom.op t)
    have hL := hres L f s
    have hN := hres N f t
    have e1 : kf W (R.map f r) =
        (X.O.obj.map f.unop.left.op) r •
          (L.val.restrictₛₗ f.unop.left.op (L.val.restrictₛₗ V.unop.hom.op s)
            ⊗ₜ[X.O.obj.obj (op W.unop.left)]
            N.val.restrictₛₗ f.unop.left.op (N.val.restrictₛₗ V.unop.hom.op t)) := by
      show (X.O.obj.map f.unop.left.op) r •
          (L.val.restrictₛₗ W.unop.hom.op s ⊗ₜ[X.O.obj.obj (op W.unop.left)]
            N.val.restrictₛₗ W.unop.hom.op t) = _
      rw [hL, hN]
    exact e1.trans hsm.symm
  let k : R ⟶ T :=
    { app := fun V => ↾(kf V)
      naturality := by
        intro V W f
        ext r
        exact hknat f r }
  have hk (V : (Over U)ᵒᵖ) : Function.Bijective (k.app V) :=
    tensor_smul_bijective (R := X.O.obj.obj (op V.unop.left)) _ _
      (hs V.unop.left V.unop.hom) (ht V.unop.left V.unop.hom)
  have : IsIso k := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun V => (ConcreteCategory.isIso_iff_bijective _).2 (hk V)
  have hR : Presheaf.IsSheaf (X.J.over U) R :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ (X.O.over U).property
  have hT : Presheaf.IsSheaf (X.J.over U) T := (Presheaf.isSheaf_of_iso_iff (asIso k)).1 hR
  let ψ := Functor.whiskerLeft (Over.forget U).op η'
  have : Presheaf.IsLocallyInjective (X.J.over U) ψ :=
    Presheaf.isLocallyInjective_whisker (X.J.over U) X.J (Over.forget U) η'
  have : Presheaf.IsLocallySurjective (X.J.over U) ψ :=
    Presheaf.isLocallySurjective_whisker (X.J.over U) X.J (Over.forget U) η'
  let q : (⟨T, hT⟩ : Sheaf (X.J.over U) (Type u)) ⟶
      (sheafCompose (X.J.over U) (forget AddCommGrpCat)).obj
        ((SheafOfModules.toSheaf _).obj (Q.over U)) := ⟨ψ⟩
  have hqi : Sheaf.IsLocallyInjective q :=
    inferInstanceAs (Presheaf.IsLocallyInjective (X.J.over U) ψ)
  have hqs : Sheaf.IsLocallySurjective q :=
    inferInstanceAs (Presheaf.IsLocallySurjective (X.J.over U) ψ)
  have : IsIso q := (Sheaf.isLocallyBijective_iff_isIso q).1 ⟨hqi, hqs⟩
  have : IsIso ψ := (sheafToPresheaf _ _).map_isIso q
  have hη : Function.Bijective (ψ.app (op (Over.mk (𝟙 U)))) :=
    ConcreteCategory.bijective_of_isIso _
  have h := hη.comp (hk (op (Over.mk (𝟙 U))))
  have hid (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (a : A.val.obj (op U)) :
      A.val.restrictₛₗ (𝟙 U).op a = a := by
    show A.val.presheaf.map (𝟙 (op U)) a = a
    simp
    rfl
  have hr (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) :
      ψ.app (op (Over.mk (𝟙 U))) (k.app (op (Over.mk (𝟙 U))) r) =
        r • tensorSection X L N U s t := by
    have h0 : k.app (op (Over.mk (𝟙 U))) r =
        @SMul.smul (X.O.obj.obj (op U)) _ _ r
          (s ⊗ₜ[X.O.obj.obj (op U)] t) := by
      show @SMul.smul (X.O.obj.obj (op U)) _ _ r
        (L.val.restrictₛₗ (𝟙 U).op s ⊗ₜ[X.O.obj.obj (op U)]
          N.val.restrictₛₗ (𝟙 U).op t) = _
      rw [hid L s, hid N t]
    rw [h0]
    exact ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 P).app (op U)).hom.map_smul r (s ⊗ₜ t)
  exact (funext hr) ▸ h

/-- The tensor product of two local generators is a local generator of the tensor product
sheaf. -/
def tensorGeneratorSections
    (L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : GeneratorSections X L U) (t : GeneratorSections X N U) :
    GeneratorSections X (tensorSheafOfModules X L N) U := by
  refine ⟨tensorSection X L N U s.val t.val, ?_⟩
  intro V f
  rw [tensorSection_restrict]
  exact tensorSection_bijective X L N V (L.val.restrictₛₗ f.op s.val)
    (N.val.restrictₛₗ f.op t.val) (generatorSections_restrict X L f s).property
    (generatorSections_restrict X N f t).property

/-- Multiplication on the two factors of a tensor product of sections multiplies the tensor
product by the product of the two scalars. -/
theorem tensorSection_smul (L N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (a b : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    tensorSection X L N U (a • s) (b • t) = (a * b) • tensorSection X L N U s t := by
  let instL : Module (X.O.obj.obj (op U)) (L.val.obj (op U)) := (L.val.obj (op U)).isModule
  let instN : Module (X.O.obj.obj (op U)) (N.val.obj (op U)) := (N.val.obj (op U)).isModule
  let a' : X.O.obj.obj (op U) := a
  let b' : X.O.obj.obj (op U) := b
  let P := (PresheafOfModules.tensorObj (O := X.O.obj) (L.val) (N.val))
  let η := (Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 P).app (op U)
  show η.hom ((a' • s) ⊗ₜ[X.O.obj.obj (op U)] (b' • t)) = (a * b) • tensorSection X L N U s t
  rw [TensorProduct.smul_tmul_smul a' b' s t]
  exact η.hom.map_smul (a' * b') (s ⊗ₜ t)

/-! ### The classification -/

variable (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    [HasSheafify X.J AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf X.J AddCommGrpCat.{u})]

/-- The first cohomology class of the generator torsor of a Picard class. -/
abbrev picardToH1
    (p : Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2) :
    Sheaf.H (unitsAddSheaf X) 1 :=
  Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X)
    (picardToTorsorClasses X hX p)

/-- The map to first cohomology is additive. -/
theorem picardToH1_add
    (p q : Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2) :
    picardToH1 X hX (p + q) = picardToH1 X hX p + picardToH1 X hX q := by
  obtain ⟨L, hL, rfl⟩ := picardGroup_exists_classOf X p
  obtain ⟨N, hN, rfl⟩ := picardGroup_exists_classOf X q
  have := hL
  have := hN
  have hM : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (tensorSheafOfModules X L N) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L N
  rw [Stacks.SheafOfModules.Picard.classOf_tensor X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L N hL hN hM]
  simp only [picardToH1]
  rw [picardToTorsorClasses_classOf X hX (tensorSheafOfModules X L N) hM,
    picardToTorsorClasses_classOf X hX L hL, picardToTorsorClasses_classOf X hX N hN]
  symm
  apply torsorClass_add_of_equivariant (unitsAddSheaf X)
    (generatorTorsor X hX L hL).torsor (generatorTorsor X hX N hN).torsor
    (generatorTorsor X hX (tensorSheafOfModules X L N) hM).torsor
    ({ app := fun U => ↾(fun s => tensorGeneratorSections X L N U.unop s.1 s.2)
       naturality := by
         intro U V f
         ext s
         exact Subtype.ext (tensorSection_restrict X L N f.unop s.1.val s.2.val).symm })
  intro U a b s t
  change Additive ((X.O.obj.obj U)ˣ) at a b
  change GeneratorSections X L U.unop at s
  change GeneratorSections X N U.unop at t
  exact Subtype.ext
    (tensorSection_smul X L N U.unop (Additive.toMul a).val (Additive.toMul b).val s.val t.val)

/-- The homomorphism from the Picard group to first cohomology of the units. -/
def picardToH1Hom :
    Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 →+
      Sheaf.H (unitsAddSheaf X) 1 where
  toFun := picardToH1 X hX
  map_add' := picardToH1_add X hX
  map_zero' := by
    have h := picardToH1_add X hX 0 0
    rw [zero_add] at h
    exact add_eq_left.mp h.symm

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf X.J AddCommGrpCat.{u})] in
/-- The class of the structure sheaf in the Picard group is zero. -/
theorem classOf_unit_eq_zero :
    Stacks.SheafOfModules.Picard.classOf X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (Stacks.SheafOfModules.isInvertible_unit X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2) = 0 := by
  have hU : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.isInvertible_unit X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
  have := hU
  have hUU : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.O.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (X.O.obj) (forget₂ CommRingCat RingCat)
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).2)⟩).obj
          ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj
          ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 _ _
  have he := (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 _ _ hUU hU).2
      ⟨Stacks.SheafOfModules.tensorSheafLeftUnitor X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 _⟩
  have h := (Stacks.SheafOfModules.Picard.classOf_tensor X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) hU hU hUU).trans he
  exact add_eq_left.mp h

/-- The map to first cohomology has trivial kernel: a trivial generator torsor gives a global
generator, hence a trivialization of the module. -/
theorem picardToH1_eq_zero
    (p : Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2)
    (hp : picardToH1 X hX p = 0) : p = 0 := by
  obtain ⟨L, hL, rfl⟩ := picardGroup_exists_classOf X p
  let F := generatorTorsor X hX L hL
  let T : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X) :=
    ⟨trivialTorsor (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf (unitsAddSheaf X)),
      trivialTorsor_isTorsor _⟩
  have heq : Quotient.mk _ F.torsor =
      Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid _) T := by
    apply (Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X)).injective
    rw [Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_trivial]
    simpa only [picardToH1, picardToTorsorClasses_classOf] using hp
  obtain ⟨e, he⟩ :=
    (Stacks.Cohomology.Torsors.torsorSetoid (unitsAddSheaf X)).symm (Quotient.exact heq)
  let s (U : X.Cᵒᵖ) : GeneratorSections X L U.unop :=
    F.sectionsEquiv U
      (e.hom.app U (Multiplicative.ofAdd (Additive.ofMul (1 : (X.O.obj.obj U)ˣ))))
  have hs {U V : X.Cᵒᵖ} (f : U ⟶ V) : L.val.restrictₛₗ f (s U).val = (s V).val := by
    have h := NatTrans.naturality_apply e.hom f
      (Multiplicative.ofAdd (Additive.ofMul (1 : (X.O.obj.obj U)ˣ)))
    have ht : T.val.presheaf.map f
        (Multiplicative.ofAdd (Additive.ofMul (1 : (X.O.obj.obj U)ˣ))) =
        Multiplicative.ofAdd (Additive.ofMul (1 : (X.O.obj.obj V)ˣ)) := by
      show Multiplicative.ofAdd ((unitsAddSheaf X).obj.map f 0) = Multiplicative.ofAdd 0
      exact congrArg Multiplicative.ofAdd (map_zero ((unitsAddSheaf X).obj.map f).hom)
    exact (F.sectionsEquiv_restrict f _).symm.trans
      (congrArg (fun z => (F.sectionsEquiv V z).val)
        (h.symm.trans (congrArg (fun z => e.hom.app V z) ht)))
  let sec : L.sections := PresheafOfModules.sectionsMk (fun U => (s U).val) (fun {_ _} f => hs f)
  let φ := L.unitHomEquiv.symm sec
  have hφ (U : X.Cᵒᵖ) : IsIso (φ.val.app U) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have h : Function.Bijective
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U => r • (s U).val) := by
      simpa using (s U).property U.unop (𝟙 U.unop)
    have hv (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) :
        (φ.val.app U).hom r = r • (s U).val := by
      rw [unitHom_symm_app_smul]
      rfl
    show Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U => (φ.val.app U).hom r)
    exact (funext hv).symm ▸ h
  let iso : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅ L :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U => @asIso _ _ _ _ (φ.val.app U) (hφ U))
        (fun {_ _} f => φ.val.naturality f))
  exact ((Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L _ hL
    (Stacks.SheafOfModules.isInvertible_unit X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2)).2 ⟨iso.symm⟩).trans
      (classOf_unit_eq_zero X)

/-- The homomorphism from the Picard group to first cohomology is bijective. -/
theorem picardToH1_bijective : Function.Bijective (picardToH1Hom X hX) :=
  ⟨(injective_iff_map_eq_zero (picardToH1Hom X hX)).2 (picardToH1_eq_zero X hX),
    (Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X)).surjective.comp
      (picardToTorsorClasses_surjective X hX)⟩

/-- The Picard group is isomorphic to first cohomology of the units. -/
@[sga "3 VIII 4.4" "Pic ≅ H¹(O^×)"]
def picardGroupAddEquivH1 :
    Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 ≃+
      Sheaf.H (unitsAddSheaf X) 1 :=
  AddEquiv.ofBijective (picardToH1Hom X hX) (picardToH1_bijective X hX)

/-- **Stacks Project, Tag 040E.** Let `(C, O)` be a locally ringed site. There is a canonical
isomorphism of abelian groups `H^1(C, O^*) = Pic(O)`. -/
@[stacks 040E, sga "3 VIII 4.4" "Pic ≅ H¹(O*)", sga "4½ Arcata 2.2.3"]
def h1UnitsAddEquivPicardGroup :
    Sheaf.H (unitsAddSheaf X) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 :=
  (picardGroupAddEquivH1 X hX).symm

/-- The inverse of the isomorphism of Tag 040E sends the class of an invertible module to the
first cohomology class of its torsor of local generators. This fixes the correspondence, rather
than only asserting that some isomorphism exists. -/
@[sga "3 VIII 4.4" "partial", sga "7 VIII 6.3" "partial"]
theorem h1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L) :
    (h1UnitsAddEquivPicardGroup X hX).symm
        (Stacks.SheafOfModules.Picard.classOf X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X)
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid (unitsAddSheaf X))
          (generatorTorsor X hX L hL).torsor) :=
  congrArg (Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X))
    (picardToTorsorClasses_classOf X hX L hL)

end Stacks.Cohomology.Torsors.Generators

end
