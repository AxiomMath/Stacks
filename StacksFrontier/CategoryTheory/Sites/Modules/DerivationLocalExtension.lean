module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.RingHom.Etale
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCokernelDerivation

/-!
# Derivations: extension along étale ring maps, and gluing from a dense family of objects

* Along an étale ring map `g : A ⟶ B`, a Leibniz map `δ : A ⟶ M` with values in a `B`-module
  (of any universe) extends to a Leibniz map `B ⟶ M`: through
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`, `Ω_B = B ⊗_A Ω_A`.
* On a site, a family of Leibniz maps `𝒪(X) ⟶ M(X)`, given only for the objects `X` of a class
  `P` whose arrows cover every object, and compatible with restriction along every morphism
  between objects of `P`, glues to a derivation of `𝒪` with values in the sheaf of modules `M`.
  If the glued map vanishes on the image of `ψ : R ⟶ 𝒪`, it is a `ψ`-derivation.
* A natural family of maps `d : A₀(X) ⟶ M(X)` out of a sheaf of sets of universe `u` into a
  sheaf of modules of an arbitrary universe vanishes at a section exactly when two morphisms of
  sheaves of sets of universe `u` agree there: `A₀` maps to the sheafified quotient of `A₀` by
  the fibres of `d`.

## Main definitions

* `Stacks.SheafOfModules.glueDerivationOfCover`: the derivation of `𝒪` with values in `M` glued
  from a compatible family of Leibniz maps over a covering class of objects.

## Main results

* `Stacks.SheafOfModules.exists_leibnizHom_extension_of_etale`: a Leibniz map extends along an
  étale ring map.
* `Stacks.SheafOfModules.glueDerivationOfCover_d`: the glued derivation takes the given value over
  every object of the class.
* `Stacks.SheafOfModules.exists_typeSheafHom_app_eq_iff`: a natural family of maps into a sheaf of
  modules vanishes at a section exactly when two morphisms of sheaves of sets agree there.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X), step M5 of its proof.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe w u v₁ u₁

namespace Stacks.SheafOfModules

/-- **A Leibniz map extends along an étale ring map**, with values in a module of an arbitrary
universe.  The module of differentials of `B` is the base change of that of `A`
(`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`). -/
theorem exists_leibnizHom_extension_of_etale {A Bb : CommRingCat.{u}} (g : A ⟶ Bb)
    (hg : g.hom.Etale) {M : Type w} [AddCommGroup M] [Module Bb M] (δ : A →+ M)
    (hmul : ∀ x y : A, δ (x * y) = g x • δ y + g y • δ x) :
    ∃ δ' : Bb →+ M, (∀ x y : Bb, δ' (x * y) = x • δ' y + y • δ' x) ∧
      ∀ x : A, δ' (g x) = δ x := by
  let := g.hom.toAlgebra
  have : Algebra.Etale A Bb := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hg
  let : Module A M := Module.compHom M g.hom
  have : IsScalarTower A Bb M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let D : Derivation ℤ A M := Derivation.mk' δ.toIntLinearMap hmul
  let L : Bb ⊗[A] KaehlerDifferential ℤ A →ₗ[Bb] M :=
    D.liftKaehlerDifferential.liftBaseChange Bb
  let D' : Derivation ℤ Bb M :=
    (L.comp (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A Bb).symm.toLinearMap).compDer
      (KaehlerDifferential.D ℤ Bb)
  refine ⟨D'.toLinearMap.toAddMonoidHom, fun x y => D'.leibniz x y, fun x => ?_⟩
  change L ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A Bb).symm
    (KaehlerDifferential.D ℤ Bb (algebraMap A Bb x))) = δ x
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  change (1 : Bb) • D.liftKaehlerDifferential (KaehlerDifferential.D ℤ A x) = δ x
  rw [one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

section Glue

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}
  {T : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
  {R : Cᵒᵖ ⥤ CommRingCat.{u}} {ψ : R ⟶ O.obj}
  (P : ObjectProperty C)
  (hP : ∀ X : C, Sieve.generate (fun (Y : C) (_ : Y ⟶ X) => P Y) ∈ J X)
  (δ : ∀ (X : C), P X → (ToType (O.obj.obj (op X)) →+ T.val.obj (op X)))
  (hnat : ∀ {X Y : C} (hX : P X) (hY : P Y) (f : X ⟶ Y) (r : ToType (O.obj.obj (op Y))),
    δ X hX (O.obj.map f.op r) = T.val.presheaf.map f.op (δ Y hY r))

omit [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
include hP hnat in
/-- Two restrictions of the given maps to a common object agree, whenever the two morphisms to
the objects of `P` lie over a common morphism to `X`. -/
theorem map_glueDerivationOfCover_family {X Y₁ Y₂ Z : C} (h₁ : P Y₁) (h₂ : P Y₂)
    (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) (hw : g₁ ≫ f₁ = g₂ ≫ f₂)
    (r : ToType (O.obj.obj (op X))) :
    T.val.presheaf.map g₁.op (δ Y₁ h₁ (O.obj.map f₁.op r)) =
      T.val.presheaf.map g₂.op (δ Y₂ h₂ (O.obj.map f₂.op r)) := by
  refine T.isSheaf.isSeparated Z _ (hP Z) _ _ ?_
  rintro W k ⟨W', k₁, k₂, hW', rfl⟩
  have e₁ := hnat hW' h₁ (k₂ ≫ g₁) (O.obj.map f₁.op r)
  have e₂ := hnat hW' h₂ (k₂ ≫ g₂) (O.obj.map f₂.op r)
  have e : O.obj.map (k₂ ≫ g₁).op (O.obj.map f₁.op r) =
      O.obj.map (k₂ ≫ g₂).op (O.obj.map f₂.op r) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, Category.assoc, Category.assoc, hw]
  have h : T.val.presheaf.map (k₂ ≫ g₁).op (δ Y₁ h₁ (O.obj.map f₁.op r)) =
      T.val.presheaf.map (k₂ ≫ g₂).op (δ Y₂ h₂ (O.obj.map f₂.op r)) := by
    rw [← e₁, ← e₂, e]
  have key : ∀ (Y' : C) (g : Z ⟶ Y') (x : T.val.obj (op Y')),
      T.val.presheaf.map (k₁ ≫ k₂).op (T.val.presheaf.map g.op x) =
        T.val.presheaf.map k₁.op (T.val.presheaf.map (k₂ ≫ g).op x) := by
    intro Y' g x
    rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
    rfl
  rw [key, key, h]

omit [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The sheaf of modules `T`, read as a sheaf of types. -/
theorem isSheaf_types_val_presheaf :
    Presieve.IsSheaf J (T.val.presheaf ⋙ forget AddCommGrpCat.{w}) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose J (forget AddCommGrpCat.{w})).obj ⟨T.val.presheaf, T.isSheaf⟩).2

/-- The family of values over the objects of `P` above `X` of the section `r`. -/
def glueDerivationOfCoverFamily (X : C) (r : ToType (O.obj.obj (op X))) :
    Presieve.FamilyOfElements (T.val.presheaf ⋙ forget AddCommGrpCat.{w})
      (fun (Y : C) (_ : Y ⟶ X) => P Y) :=
  fun _ f hY => δ _ hY (O.obj.map f.op r)

omit [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
include hP hnat in
/-- The family of values over the objects of `P` above `X` of the section `r` is compatible. -/
theorem glueDerivationOfCoverFamily_compatible (X : C) (r : ToType (O.obj.obj (op X))) :
    (glueDerivationOfCoverFamily P δ X r).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hw
  exact map_glueDerivationOfCover_family P hP δ hnat h₁ h₂ f₁ f₂ g₁ g₂ hw r

/-- The glued value over `X` of a section `r`. -/
def glueDerivationOfCoverValue (X : C) (r : ToType (O.obj.obj (op X))) : T.val.obj (op X) :=
  ((isSheaf_types_val_presheaf (T := T)).isSheafFor _ (hP X)).amalgamate _
    (glueDerivationOfCoverFamily_compatible P hP δ hnat X r)

omit [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The glued value over `X` of a section `r` restricts, over an object `Y` of `P` above `X`, to
the value of `δ Y` at the restriction of `r`. -/
theorem glueDerivationOfCoverValue_map {X Y : C} (hY : P Y) (f : Y ⟶ X)
    (r : ToType (O.obj.obj (op X))) :
    T.val.presheaf.map f.op (glueDerivationOfCoverValue P hP δ hnat X r) =
      δ Y hY (O.obj.map f.op r) :=
  ((isSheaf_types_val_presheaf (T := T)).isSheafFor _ (hP X)).valid_glue _ f hY

omit [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `Stacks.SheafOfModules.glueDerivationOfCoverValue_map`, with the restriction map of the
presheaf of modules in place of that of its underlying presheaf of abelian groups. -/
theorem glueDerivationOfCoverValue_map_val {X Y : C} (hY : P Y) (f : Y ⟶ X)
    (r : ToType (O.obj.obj (op X))) :
    T.val.map f.op (glueDerivationOfCoverValue P hP δ hnat X r) = δ Y hY (O.obj.map f.op r) :=
  glueDerivationOfCoverValue_map P hP δ hnat hY f r

omit [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
include hP in
/-- Two sections of `T` over `X` agreeing over every object of `P` above `X` are equal. -/
theorem eq_of_forall_map_eq_of_cover {X : C} (s t : T.val.obj (op X))
    (h : ∀ (Y : C), P Y → ∀ (f : Y ⟶ X), T.val.presheaf.map f.op s = T.val.presheaf.map f.op t) :
    s = t :=
  ((isSheaf_types_val_presheaf (T := T)).isSheafFor _ (hP X)).isSeparatedFor.ext
    fun Y f hY => h Y hY f

omit [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The glued value of the restriction of `r` along `f : X' ⟶ X` is the restriction along `f` of
the glued value of `r`. -/
theorem glueDerivationOfCoverValue_naturality {X X' : C} (f : X' ⟶ X)
    (r : ToType (O.obj.obj (op X))) :
    glueDerivationOfCoverValue P hP δ hnat X' (O.obj.map f.op r) =
      T.val.presheaf.map f.op (glueDerivationOfCoverValue P hP δ hnat X r) :=
  eq_of_forall_map_eq_of_cover P hP _ _ fun Y hY g => by
    refine (glueDerivationOfCoverValue_map P hP δ hnat hY g _).trans ?_
    have := glueDerivationOfCoverValue_map P hP δ hnat hY (g ≫ f) r
    rw [op_comp, Functor.map_comp, Functor.map_comp] at this
    exact this.symm

omit [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The glued value of the zero section is zero. -/
theorem glueDerivationOfCoverValue_zero (X : C) :
    glueDerivationOfCoverValue P hP δ hnat X 0 = 0 :=
  eq_of_forall_map_eq_of_cover P hP _ _ fun Y hY f =>
    (glueDerivationOfCoverValue_map_val P hP δ hnat hY f 0).trans
      (((congrArg (δ Y hY) (map_zero _)).trans (map_zero _)).trans
        (map_zero (T.val.map f.op).hom).symm)

omit [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Vanishing of a natural family of maps into a sheaf of modules, as an equality of
morphisms of sheaves of sets of a smaller universe.**  Let `A₀` be a sheaf of sets of universe
`u`, `z` a natural family of sections of `A₀`, and `d : A₀(X) ⟶ M(X)` a natural family of maps
into a sheaf of modules `M` of an arbitrary universe with `d z = 0`.  Then there are a sheaf of
sets `E` of universe `u` and morphisms `ε ε' : A₀ ⟶ E` with `ε a = ε' a ⟺ d a = 0`: take for `E`
the sheafification of the quotient of `A₀` by the fibres of `d`, for `ε` the quotient map and for
`ε'` the constant map at the class of `z`.  The sheafification map is locally injective and `M` is
separated. -/
theorem exists_typeSheafHom_app_eq_iff [HasWeakSheafify J (Type u)]
    [J.WEqualsLocallyBijective (Type u)] (A₀ : Sheaf J (Type u)) (z : ∀ X : Cᵒᵖ, A₀.obj.obj X)
    (hz : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), A₀.obj.map f (z X) = z Y)
    (d : ∀ X : Cᵒᵖ, A₀.obj.obj X → T.val.obj X)
    (hd : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : A₀.obj.obj X),
      d Y (A₀.obj.map f a) = T.val.presheaf.map f (d X a))
    (hdz : ∀ X : Cᵒᵖ, d X (z X) = 0) :
    ∃ (E : Sheaf J (Type u)) (ε ε' : A₀ ⟶ E),
      ∀ (X : Cᵒᵖ) (a : A₀.obj.obj X), ε.hom.app X a = ε'.hom.app X a ↔ d X a = 0 := by
  let Q : Cᵒᵖ ⥤ Type u :=
    { obj X := Quotient (Setoid.ker (d X))
      map {X Y} f := ↾(Quotient.map' (A₀.obj.map f) (fun a b (h : d X a = d X b) =>
        show d Y _ = d Y _ by rw [hd, hd, h]))
      map_id X := by
        ext ⟨a⟩
        exact congrArg (Quotient.mk (Setoid.ker (d X))) (A₀.obj.map_id_apply _ a)
      map_comp {X Y Z} f g := by
        ext ⟨a⟩
        exact congrArg (Quotient.mk (Setoid.ker (d Z)))
          (A₀.obj.map_comp_apply f g a) }
  let q : A₀.obj ⟶ Q :=
    { app X := ↾(fun a => Quotient.mk (Setoid.ker (d X)) a)
      naturality _ _ _ := rfl }
  let q' : A₀.obj ⟶ Q :=
    { app X := ↾(fun _ => Quotient.mk (Setoid.ker (d X)) (z X))
      naturality X Y f := by
        ext a
        exact congrArg (Quotient.mk (Setoid.ker (d Y))) (hz f).symm }
  refine ⟨(presheafToSheaf J _).obj Q, ObjectProperty.homMk (q ≫ toSheafify J Q),
    ObjectProperty.homMk (q' ≫ toSheafify J Q), fun X a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hs := Presheaf.equalizerSieve_mem J (toSheafify J Q)
      (Quotient.mk (Setoid.ker (d X)) a) (Quotient.mk (Setoid.ker (d X)) (z X)) h
    refine (T.isSheaf.isSeparated X.unop _ hs (d X a) 0 fun Y g hg => ?_)
    have e : d (op Y) (A₀.obj.map g.op a) = d (op Y) (A₀.obj.map g.op (z X)) := Quotient.exact hg
    rw [hd, hd, hdz] at e
    exact e
  · have e : Quotient.mk (Setoid.ker (d X)) a =
        Quotient.mk (Setoid.ker (d X)) (z X) :=
      Quotient.sound (show d X a = d X (z X) from h.trans (hdz X).symm)
    exact congrArg ((toSheafify J Q).app X) e

variable (hmul : ∀ (X : C) (hX : P X) (a b : ToType (O.obj.obj (op X))),
    δ X hX (a * b) = a • δ X hX b + b • δ X hX a)
  (happ : ∀ (X : Cᵒᵖ) (a : ToType (R.obj X)),
    glueDerivationOfCoverValue P hP δ hnat X.unop (ψ.app X a) = 0)

/-- **Gluing a derivation from a covering class of objects.**  A family of Leibniz maps
`𝒪(X) ⟶ T(X)` over the objects `X` of `P`, compatible with restriction along the morphisms
between them, is the family of values of a unique derivation of `𝒪` with values in `T`, as
soon as the objects of `P` cover every object; it is a `ψ`-derivation when the glued map vanishes
on the image of `ψ`. -/
def glueDerivationOfCover : PresheafOfModulesOfCommRing.Derivation' T.val ψ where
  d {X} :=
    { toFun := glueDerivationOfCoverValue P hP δ hnat X.unop
      map_zero' := glueDerivationOfCoverValue_zero P hP δ hnat X.unop
      map_add' := fun a b => eq_of_forall_map_eq_of_cover P hP _ _ fun Y hY f =>
        (glueDerivationOfCoverValue_map_val P hP δ hnat hY f (a + b)).trans
          (((congrArg (δ Y hY) (map_add _ a b)).trans (map_add _ _ _)).trans
            ((congrArg₂ (· + ·) (glueDerivationOfCoverValue_map_val P hP δ hnat hY f a).symm
              (glueDerivationOfCoverValue_map_val P hP δ hnat hY f b).symm).trans
                (map_add (T.val.map f.op).hom _ _).symm)) }
  d_mul {X} a b := eq_of_forall_map_eq_of_cover P hP _ _ fun Y hY f => by
    refine (glueDerivationOfCoverValue_map_val P hP δ hnat hY f (a * b)).trans ?_
    refine ((congrArg (δ Y hY) (map_mul _ a b)).trans (hmul Y hY _ _)).trans ?_
    have h1 := PresheafOfModules.map_smul T.val f.op a
      (glueDerivationOfCoverValue P hP δ hnat X.unop b)
    have h2 := PresheafOfModules.map_smul T.val f.op b
      (glueDerivationOfCoverValue P hP δ hnat X.unop a)
    rw [glueDerivationOfCoverValue_map_val] at h1 h2
    exact (congrArg₂ (· + ·) h1.symm h2.symm).trans (map_add (T.val.map f.op).hom _ _).symm
  d_map {X X'} f a := glueDerivationOfCoverValue_naturality P hP δ hnat f.unop a
  d_app {X} a := happ X a

omit [HasWeakSheafify J CommRingCat.{u}] in
include hnat in
/-- The glued derivation takes the given value over an object of `P`. -/
theorem glueDerivationOfCover_d (X : C) (hX : P X) (r : ToType (O.obj.obj (op X))) :
    (glueDerivationOfCover P hP δ hnat hmul happ).d (X := op X) r = δ X hX r := by
  refine eq_of_forall_map_eq_of_cover P hP _ _ fun Y hY f => ?_
  exact (glueDerivationOfCoverValue_map P hP δ hnat hY f r).trans (hnat hY hX f r)

end Glue

end Stacks.SheafOfModules

end
