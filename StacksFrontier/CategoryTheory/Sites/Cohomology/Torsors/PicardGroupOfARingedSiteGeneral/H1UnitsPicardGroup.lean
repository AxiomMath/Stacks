module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSiteGeneral.GeneratorTorsor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSiteGeneral.CoefficientModule
import StacksCore.Tactic.StacksAttribute

/-!
# The Picard group of a ringed site and `H^1(C, O^*)`, with independent universes

The map from Picard classes to classes of unit torsors, products of torsors and the additivity of
the classification, tensor products of local generators, and Tag 040E,
`Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup'`, over a ringed site
`AlgebraicGeometry.RingedSite.{u, v, w}` with the three universes independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory

universe u v w t

namespace Stacks.Cohomology.Torsors.Generators

attribute [local instance] coefficientFamilyModule'

/-! ### From Picard classes to torsor classes -/

/-- The generator-torsor class of a Picard class: the class of the generator torsor of the
chosen representative of the corresponding isomorphism class of invertible modules.

This generalizes `Stacks.Cohomology.Torsors.Generators.picardToTorsorClasses`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def picardToTorsorClasses' (X : RingedSite.{u, v, w})
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] :
    Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 →
      Stacks.Cohomology.Torsors.torsorIsoClasses (unitsAddSheaf X) :=
  fun p => Quotient.lift
    (fun L : Stacks.SheafOfModules.InvertibleModules X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 =>
      Quotient.mk _ (generatorTorsor' X hX L.obj L.property).torsor)
    (by
      intro L N h
      obtain ⟨e⟩ := h
      exact Quotient.sound (generatorTorsor_isIsomorphic_of_iso' X
        ((ObjectProperty.ι _).mapIso e)
        (generatorTorsor' X hX L.obj L.property)
        (generatorTorsor' X hX N.obj N.property)))
    ((Stacks.SheafOfModules.Picard.picardGroupData X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2).classEquiv.symm p)

/-- On the class of an invertible module the map is the class of its generator torsor.

This generalizes `Stacks.Cohomology.Torsors.Generators.picardToTorsorClasses_classOf`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem picardToTorsorClasses_classOf' (X : RingedSite.{u, v, w})
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L) :
    picardToTorsorClasses' X hX
        (Stacks.SheafOfModules.Picard.classOf X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL) =
      Quotient.mk _ (generatorTorsor' X hX L hL).torsor := by
  simp only [picardToTorsorClasses', Stacks.SheafOfModules.Picard.classOf,
    Equiv.symm_apply_apply]
  rfl

/-- **Every torsor comes from an invertible module.**

This generalizes `Stacks.Cohomology.Torsors.Generators.picardToTorsorClasses_surjective`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem picardToTorsorClasses_surjective' (X : RingedSite.{u, v, w})
    [EssentiallySmall.{w} X.C]
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] :
    Function.Surjective (picardToTorsorClasses' X hX) := by
  intro c
  induction c using Quotient.inductionOn with
  | h F =>
    refine ⟨Stacks.SheafOfModules.Picard.classOf X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (coefficientSheaf' X F)
      (coefficientSheaf_isInvertible' X F), ?_⟩
    rw [picardToTorsorClasses_classOf']
    exact Quotient.sound ((Stacks.Cohomology.Torsors.torsorSetoid (unitsAddSheaf X)).symm
      (coefficientGeneratorTorsor_isIsomorphic' X F hX))

/-- Every Picard class is the class of an invertible module.

This generalizes `Stacks.Cohomology.Torsors.Generators.picardGroup_exists_classOf`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem picardGroup_exists_classOf' (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    (p : Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2) :
    ∃ (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L),
      Stacks.SheafOfModules.Picard.classOf X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
        L hL = p := by
  obtain ⟨c, rfl⟩ :=
    (Stacks.SheafOfModules.Picard.picardGroupData X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2).classEquiv.surjective p
  induction c using Quotient.inductionOn with
  | h L => exact ⟨L.obj, L.property, rfl⟩

/-! ### Products of torsors and additivity of the classification -/

/-- The product of two presheaves of sets.

This generalizes `Stacks.Cohomology.Torsors.Generators.productPresheaf`,
stated with the sections in the universe of the objects of the site, to independent
universes. -/
def productPresheaf' {D : Type u} [Category.{v} D] (F G : Dᵒᵖ ⥤ Type w) : Dᵒᵖ ⥤ Type w where
  obj U := F.obj U × G.obj U
  map f := ↾(fun s => (F.map f s.1, G.map f s.2))
  map_id U := by ext s <;> simp
  map_comp f g := by ext s <;> simp

/-- The product of two sheaves of sets is a sheaf.

This generalizes `Stacks.Cohomology.Torsors.Generators.productPresheaf_isSheaf`,
stated with the sections in the universe of the objects of the site, to independent
universes. -/
theorem productPresheaf_isSheaf' {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology D) {F G : Dᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf J F) (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J (productPresheaf' F G) := by
  apply (isSheaf_iff_isSheaf_of_type J _).2
  intro U S hS x hx
  have key {E : Dᵒᵖ ⥤ Type w} (hE : Presheaf.IsSheaf J E) (π : productPresheaf' F G ⟶ E) :
      ∃! e : E.obj (op U), ∀ ⦃V⦄ (a : V ⟶ U) (ha : S.arrows a), E.map a.op e = π.app _ (x a ha) :=
    hE.isSheafFor S hS (fun V f hf => π.app _ (x f hf)) fun V W T a b f g hf hg h =>
      (π.naturality_apply _ _).symm.trans
        ((congrArg (π.app _) (hx a b hf hg h)).trans (π.naturality_apply _ _))
  obtain ⟨f, hf, hfu⟩ := key hF ⟨fun _ => ↾Prod.fst, fun _ _ _ => rfl⟩
  obtain ⟨g, hg, hgu⟩ := key hG ⟨fun _ => ↾Prod.snd, fun _ _ _ => rfl⟩
  exact ⟨(f, g), fun V a ha => Prod.ext (hf a ha) (hg a ha), fun y hy =>
    Prod.ext (hfu _ fun V a ha => congrArg Prod.fst (hy a ha))
      (hgu _ fun V a ha => congrArg Prod.snd (hy a ha))⟩

/-- The product of two abelian sheaves.

This generalizes `Stacks.Cohomology.Torsors.Generators.productAbelianSheaf`,
stated with the sections in the universe of the objects of the site, to independent
universes. -/
def productAbelianSheaf' {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology D} (H K : Sheaf J AddCommGrpCat.{w}) :
    Sheaf J AddCommGrpCat.{w} := by
  let P : Dᵒᵖ ⥤ AddCommGrpCat.{w} := {
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
  refine ⟨P, fun E => ?_⟩
  let eU (U : Dᵒᵖ) : ((H.obj ⋙ coyoneda.obj (op E)).obj U ×
      (K.obj ⋙ coyoneda.obj (op E)).obj U) ≃ (P ⋙ coyoneda.obj (op E)).obj U :=
    { toFun := fun fg => AddCommGrpCat.ofHom (fg.1.hom.prod fg.2.hom)
      invFun := fun f => (f ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _),
        f ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _))
      left_inv := fun fg => rfl
      right_inv := fun f => by apply ConcreteCategory.hom_ext; intro x; rfl }
  let e : productPresheaf' (H.obj ⋙ coyoneda.obj (op E)) (K.obj ⋙ coyoneda.obj (op E)) ≅
      P ⋙ coyoneda.obj (op E) :=
    NatIso.ofComponents (fun U => (eU U).toIso) (by
      intro U V f
      ext fg
      apply ConcreteCategory.hom_ext
      intro x
      rfl)
  exact (isSheaf_iff_isSheaf_of_type J _).1 ((Presheaf.isSheaf_of_iso_iff e).1
    (productPresheaf_isSheaf' J
      ((isSheaf_iff_isSheaf_of_type J _).2 (H.property E))
      ((isSheaf_iff_isSheaf_of_type J _).2 (K.property E))))

/-- The first projection out of a product of abelian sheaves.

This generalizes `Stacks.Cohomology.Torsors.Generators.productAbelianSheafFst`,
stated with the sections in the universe of the objects of the site, to independent
universes. -/
def productAbelianSheafFst' {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology D} (H K : Sheaf J AddCommGrpCat.{w}) :
    productAbelianSheaf' H K ⟶ H where
  hom.app _ := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
  hom.naturality _ _ _ := rfl

/-- The second projection out of a product of abelian sheaves.

This generalizes `Stacks.Cohomology.Torsors.Generators.productAbelianSheafSnd`,
stated with the sections in the universe of the objects of the site, to independent
universes. -/
def productAbelianSheafSnd' {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology D} (H K : Sheaf J AddCommGrpCat.{w}) :
    productAbelianSheaf' H K ⟶ K where
  hom.app _ := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
  hom.naturality _ _ _ := rfl

/-- The product of two torsors, a torsor under the product of the two coefficient sheaves.

This generalizes `Stacks.Cohomology.Torsors.Generators.productAbelianTorsor`,
stated with the sections in the universe of the objects of the site, to independent
universes. -/
def productAbelianTorsor' {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology D} {H K : Sheaf J AddCommGrpCat.{w}}
    (F : Stacks.Cohomology.Torsors.AbelianTorsor H)
    (G : Stacks.Cohomology.Torsors.AbelianTorsor K) :
    Stacks.Cohomology.Torsors.AbelianTorsor (productAbelianSheaf' H K) := by
  let P : PseudoTorsor
      (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf (productAbelianSheaf' H K)) := {
    presheaf := productPresheaf' F.1.presheaf G.1.presheaf
    isSheaf := productPresheaf_isSheaf' J F.1.isSheaf G.1.isSheaf
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
third one adds the acting sections, then the class of the third is the sum of the two classes.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorClass_add_of_equivariant`,
stated with the sections in the universe of the objects of the site, to independent
universes. -/
theorem torsorClass_add_of_equivariant' {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology D} [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{t} (Sheaf J AddCommGrpCat.{w})] (H : Sheaf J AddCommGrpCat.{w})
    (F G T : Stacks.Cohomology.Torsors.AbelianTorsor H)
    (f : productPresheaf' F.1.presheaf G.1.presheaf ⟶ T.1.presheaf)
    (hf : ∀ (U : Dᵒᵖ) (a b : H.obj.obj U) (s : F.1.presheaf.obj U) (t : G.1.presheaf.obj U),
      f.app U (F.1.act U (Multiplicative.ofAdd a) s,
        G.1.act U (Multiplicative.ofAdd b) t) =
      T.1.act U (Multiplicative.ofAdd (a + b)) (f.app U (s, t))) :
    Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H (Quotient.mk _ F) +
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H (Quotient.mk _ G) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H (Quotient.mk _ T) := by
  let P := productAbelianTorsor' F G
  let p := productAbelianSheafFst' H H
  let q := productAbelianSheafSnd' H H
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

section

variable (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]

/-- Multiplication by the tensor product of two local generators is bijective: on the slice
site the multiplication map is the sheafification of an isomorphism.

This generalizes `Stacks.Cohomology.Torsors.Generators.tensorSection_bijective`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem tensorSection_bijective'
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : GeneratorSections' X L U) (t : GeneratorSections' X N U) :
    Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) =>
      r • tensorSection X L N U s.val t.val) := by
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
    r • (L.val.restrictₛₗ V.unop.hom.op s.val ⊗ₜ[X.O.obj.obj (op V.unop.left)]
      N.val.restrictₛₗ V.unop.hom.op t.val)
  have hres (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
      (m : M.val.obj (op U)) :
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
      (L.val.restrictₛₗ V.unop.hom.op s.val ⊗ₜ[X.O.obj.obj (op V.unop.left)]
        N.val.restrictₛₗ V.unop.hom.op t.val)
    have hL := hres L f s.val
    have hN := hres N f t.val
    have e1 : kf W (R.map f r) =
        (X.O.obj.map f.unop.left.op) r •
          (L.val.restrictₛₗ f.unop.left.op (L.val.restrictₛₗ V.unop.hom.op s.val)
            ⊗ₜ[X.O.obj.obj (op W.unop.left)]
            N.val.restrictₛₗ f.unop.left.op (N.val.restrictₛₗ V.unop.hom.op t.val)) := by
      show (X.O.obj.map f.unop.left.op) r •
          (L.val.restrictₛₗ W.unop.hom.op s.val ⊗ₜ[X.O.obj.obj (op W.unop.left)]
            N.val.restrictₛₗ W.unop.hom.op t.val) = _
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
      (s.property V.unop.left V.unop.hom) (t.property V.unop.left V.unop.hom)
  have : IsIso k := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun V => (ConcreteCategory.isIso_iff_bijective _).2 (hk V)
  have hR : Presheaf.IsSheaf (X.J.over U) R :=
    Presheaf.isSheaf_comp_of_isSheaf (X.J.over U) (X.O.over U).obj
      (forget CommRingCat.{w}) (X.O.over U).property
  have hT : Presheaf.IsSheaf (X.J.over U) T := (Presheaf.isSheaf_of_iso_iff (asIso k)).1 hR
  let ψ := Functor.whiskerLeft (Over.forget U).op η'
  have : Presheaf.IsLocallyInjective (X.J.over U) ψ :=
    Presheaf.isLocallyInjective_whisker (X.J.over U) X.J (Over.forget U) η'
  have : Presheaf.IsLocallySurjective (X.J.over U) ψ :=
    Presheaf.isLocallySurjective_whisker (X.J.over U) X.J (Over.forget U) η'
  let q : (⟨T, hT⟩ : Sheaf (X.J.over U) (Type w)) ⟶
      (sheafCompose (X.J.over U) (forget AddCommGrpCat.{w})).obj
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
  have hid (A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (a : A.val.obj (op U)) :
      A.val.restrictₛₗ (𝟙 U).op a = a := by
    show A.val.presheaf.map (𝟙 (op U)) a = a
    simp
    rfl
  have hr (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) :
      ψ.app (op (Over.mk (𝟙 U))) (k.app (op (Over.mk (𝟙 U))) r) =
        r • tensorSection X L N U s.val t.val := by
    have h0 : k.app (op (Over.mk (𝟙 U))) r =
        @SMul.smul (X.O.obj.obj (op U)) _ _ r
          (s.val ⊗ₜ[X.O.obj.obj (op U)] t.val) := by
      show @SMul.smul (X.O.obj.obj (op U)) _ _ r
        (L.val.restrictₛₗ (𝟙 U).op s.val ⊗ₜ[X.O.obj.obj (op U)]
          N.val.restrictₛₗ (𝟙 U).op t.val) = _
      rw [hid L s.val, hid N t.val]
    rw [h0]
    exact ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 P).app
      (op U)).hom.map_smul r (s.val ⊗ₜ t.val)
  exact (funext hr) ▸ h

/-- The tensor product of two local generators is a local generator of the tensor product
sheaf.

This generalizes `Stacks.Cohomology.Torsors.Generators.tensorGeneratorSections`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def tensorGeneratorSections' (L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : GeneratorSections' X L U) (t : GeneratorSections' X N U) :
    GeneratorSections' X (tensorSheafOfModules X L N) U := by
  refine ⟨tensorSection X L N U s.val t.val, ?_⟩
  intro V f
  rw [tensorSection_restrict]
  exact tensorSection_bijective' X L N V (generatorSections_restrict' X L f s)
    (generatorSections_restrict' X N f t)

/-- Multiplication on the two factors of a tensor product of sections multiplies the tensor
product by the product of the two scalars.

This generalizes `Stacks.Cohomology.Torsors.Generators.tensorSection_smul`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem tensorSection_smul' (L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (a b : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    tensorSection X L N U (a • s) (b • t) = (a * b) • tensorSection X L N U s t := by
  let instL : Module (X.O.obj.obj (op U)) (L.val.obj (op U)) := (L.val.obj (op U)).isModule
  let instN : Module (X.O.obj.obj (op U)) (N.val.obj (op U)) := (N.val.obj (op U)).isModule
  let a' : X.O.obj.obj (op U) := a
  let b' : X.O.obj.obj (op U) := b
  let P := (PresheafOfModules.tensorObj (O := X.O.obj) (L.val) (N.val))
  let η := (Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 P).app
    (op U)
  have h1 : (a' • s) ⊗ₜ[X.O.obj.obj (op U)] (b' • t) =
      (a' * b') • (s ⊗ₜ[X.O.obj.obj (op U)] t) := TensorProduct.smul_tmul_smul a' b' s t
  show η.hom ((a' • s) ⊗ₜ[X.O.obj.obj (op U)] (b' • t)) = (a * b) • tensorSection X L N U s t
  rw [h1]
  exact η.hom.map_smul (a' * b') (s ⊗ₜ t)

/-! ### The classification -/

variable (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    [HasSheafify X.J AddCommGrpCat.{w}]
    [HasExt.{t} (Sheaf X.J AddCommGrpCat.{w})]

/-- The first cohomology class of the generator torsor of a Picard class.

This generalizes `Stacks.Cohomology.Torsors.Generators.picardToH1`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
abbrev picardToH1'
    (p : Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2) :
    Sheaf.H (unitsAddSheaf X) 1 :=
  Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X)
    (picardToTorsorClasses' X hX p)

/-- The map to first cohomology is additive.

This generalizes `Stacks.Cohomology.Torsors.Generators.picardToH1_add`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem picardToH1_add'
    (p q : Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2) :
    picardToH1' X hX (p + q) = picardToH1' X hX p + picardToH1' X hX q := by
  obtain ⟨L, hL, rfl⟩ := picardGroup_exists_classOf' X p
  obtain ⟨N, hN, rfl⟩ := picardGroup_exists_classOf' X q
  have := hL
  have := hN
  have hM : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      (tensorSheafOfModules X L N) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L N
  have hadd : Stacks.SheafOfModules.Picard.classOf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL +
      Stacks.SheafOfModules.Picard.classOf X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
        N hN =
      Stacks.SheafOfModules.Picard.classOf X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
        (tensorSheafOfModules X L N) hM :=
    Stacks.SheafOfModules.Picard.classOf_tensor X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L N hL hN hM
  rw [hadd]
  simp only [picardToH1']
  rw [picardToTorsorClasses_classOf' X hX (tensorSheafOfModules X L N) hM,
    picardToTorsorClasses_classOf' X hX L hL, picardToTorsorClasses_classOf' X hX N hN]
  symm
  apply torsorClass_add_of_equivariant' (unitsAddSheaf X)
    (generatorTorsor' X hX L hL).torsor (generatorTorsor' X hX N hN).torsor
    (generatorTorsor' X hX (tensorSheafOfModules X L N) hM).torsor
    ({ app := fun U => ↾(fun s => tensorGeneratorSections' X L N U.unop s.1 s.2)
       naturality := by
         intro U V f
         ext s
         apply Subtype.ext
         exact (tensorSection_restrict X L N f.unop s.1.val s.2.val).symm })
  intro U a b s t
  change Additive ((X.O.obj.obj U)ˣ) at a b
  change GeneratorSections' X L U.unop at s
  change GeneratorSections' X N U.unop at t
  apply Subtype.ext
  exact tensorSection_smul' X L N U.unop (Additive.toMul a).val (Additive.toMul b).val s.val t.val

/-- The homomorphism from the Picard group to first cohomology of the units.

This generalizes `Stacks.Cohomology.Torsors.Generators.picardToH1Hom`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def picardToH1Hom' :
    Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 →+
      Sheaf.H (unitsAddSheaf X) 1 where
  toFun := picardToH1' X hX
  map_add' := picardToH1_add' X hX
  map_zero' := by
    have h := picardToH1_add' X hX 0 0
    rw [zero_add] at h
    exact (add_eq_left.mp h.symm)

/-- The class of the structure sheaf in the Picard group is zero.

This generalizes `Stacks.Cohomology.Torsors.Generators.classOf_unit_eq_zero`,
stated for `RingedSite.{u, u, u}`, to independent universes; the universe-polymorphic ringed
site and the hypotheses on it are spelled out in the signature. -/
theorem classOf_unit_eq_zero' (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [HasSheafify X.J AddCommGrpCat.{w}] [HasExt.{t} (Sheaf X.J AddCommGrpCat.{w})] :
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
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.O.obj) (forget₂ CommRingCat RingCat)
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
generator, hence a trivialization of the module.

This generalizes `Stacks.Cohomology.Torsors.Generators.picardToH1_eq_zero`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem picardToH1_eq_zero'
    (p : Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2)
    (hp : picardToH1' X hX p = 0) : p = 0 := by
  obtain ⟨L, hL, rfl⟩ := picardGroup_exists_classOf' X p
  let F := generatorTorsor' X hX L hL
  let T : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X) :=
    ⟨trivialTorsor (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf (unitsAddSheaf X)),
      trivialTorsor_isTorsor _⟩
  have heq : Quotient.mk _ F.torsor =
      Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid _) T := by
    apply (Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X)).injective
    rw [Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_trivial]
    simpa only [picardToH1', picardToTorsorClasses_classOf'] using hp
  obtain ⟨e, he⟩ :=
    (Stacks.Cohomology.Torsors.torsorSetoid (unitsAddSheaf X)).symm (Quotient.exact heq)
  let s (U : X.Cᵒᵖ) : GeneratorSections' X L U.unop :=
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
      rw [unitHom_symm_app_smul']
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
      (classOf_unit_eq_zero' X)

end

/-! ### Surjectivity and the isomorphism of Tag 040E -/

section

variable (X : RingedSite.{u, v, w}) [EssentiallySmall.{w} X.C]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    [HasSheafify X.J AddCommGrpCat.{w}]
    [HasExt.{t} (Sheaf X.J AddCommGrpCat.{w})]

/-- The homomorphism from the Picard group to first cohomology is bijective.

This generalizes `Stacks.Cohomology.Torsors.Generators.picardToH1_bijective`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem picardToH1_bijective' : Function.Bijective (picardToH1Hom' X hX) :=
  ⟨(injective_iff_map_eq_zero (picardToH1Hom' X hX)).2 (picardToH1_eq_zero' X hX),
    (Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X)).surjective.comp
      (picardToTorsorClasses_surjective' X hX)⟩

/-- The Picard group is isomorphic to first cohomology of the units.

This generalizes `Stacks.Cohomology.Torsors.Generators.picardGroupAddEquivH1`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
@[sga "1 XI 6.4" "more general", sga "3 VIII 4.4" "Pic ≅ H¹(O^×)"]
def picardGroupAddEquivH1' :
    Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 ≃+
      Sheaf.H (unitsAddSheaf X) 1 :=
  AddEquiv.ofBijective (picardToH1Hom' X hX) (picardToH1_bijective' X hX)

/-- **Stacks Project, Tag 040E.** Let `(C, O)` be a locally ringed site. There is a canonical
isomorphism of abelian groups `H^1(C, O^*) = Pic(O)`.

This generalizes `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
@[stacks 040E "with the three universes of the ringed site independent, on a site essentially \
small at the universe of the sections of the structure sheaf"]
def h1UnitsAddEquivPicardGroup' :
    Sheaf.H (unitsAddSheaf X) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 :=
  (picardGroupAddEquivH1' X hX).symm

/-- The inverse of the isomorphism of Tag 040E sends the class of an invertible module to the
first cohomology class of its torsor of local generators. This fixes the correspondence, rather
than only asserting that some isomorphism exists.

This generalizes `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
@[sga "3 VIII 4.4" "partial", sga "7 VIII 6.3" "partial"]
theorem h1UnitsAddEquivPicardGroup_symm_classOf'
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L) :
    (h1UnitsAddEquivPicardGroup' X hX).symm
        (Stacks.SheafOfModules.Picard.classOf X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X)
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid (unitsAddSheaf X))
          (generatorTorsor' X hX L hL).torsor) :=
  congrArg (Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 (unitsAddSheaf X))
    (picardToTorsorClasses_classOf' X hX L hL)

end

end Stacks.Cohomology.Torsors.Generators

end
