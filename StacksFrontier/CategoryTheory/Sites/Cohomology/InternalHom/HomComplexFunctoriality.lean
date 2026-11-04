module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
import StacksCore.Tactic.StacksAttribute

/-! # Functoriality of the internal Hom complex on a ringed site

Let `(C, O)` be a ringed site. The internal Hom complex `SheafHom(K, M)` of two cochain
complexes of `O`-modules is constructed in `StacksDraft.Ch21.Sec34.InternalHomComplexOnASite`,
where it is characterised by the identification of its sections over an object `U` with the
ordinary Hom complex of the restrictions `K|_U` and `M|_U`, together with the compatibility of
those identifications with restriction along arrows of the site and with the action of the
sections of the structure sheaf.

This file makes that internal Hom complex functorial: a morphism `k : K' ⟶ K` and a morphism
`m : M ⟶ M'` induce a morphism `SheafHom(K, M) ⟶ SheafHom(K', M')`, acting on sections by
ordinary pre- and postcomposition with the restrictions of `k` and `m`. This is the
functoriality that the currying isomorphism of Stacks 0A90 is natural for.

## Main definitions

* `AlgebraicGeometry.RingedSite.cochainConj`: pre- and postcomposition of a cochain between
  restricted complexes with the restrictions of morphisms in each variable.
* `AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`: the characterising
  identification of the sections of the internal Hom complex over `U` in degree `n` with the
  degree-`n` cochains from `K|_U` to `M|_U`, as an additive equivalence.
* `AlgebraicGeometry.RingedSite.homMap`: the induced morphism of internal Hom complexes.

## Main results

* `AlgebraicGeometry.RingedSite.sectionsIso_homMap_v`: `homMap k m` acts on sections by pre-
  and postcomposition with `k` and `m`.
* `AlgebraicGeometry.RingedSite.homMap_id`: the identities induce the identity.

## Implementation notes

The internal Hom complex is only available through its characterising data, so the induced
morphism is built from that data rather than from a formula: on sections over `U` it is the
conjugate, by `sectionsEquiv`, of the pre- and postcomposition operation `cochainConj` on
cochains. That it is a morphism of *sheaves of modules*, and not merely of sheaves of abelian
groups, is exactly the content of the `smul_natural` field of `SheafHomComplex`, and that it is
a morphism of *complexes* is the content of `sectionsIso` being an isomorphism of complexes
together with `cochainConj_δ`.

The universes are those of `StacksDraft.Ch21.Sec34.InternalHomComplexOnASite`: the objects of
the site, its morphisms, the sections of the structure sheaf and the sections of the modules
carry four independent universes, and nothing here constrains them, since the induced morphism
is built from the characterising data rather than from the internal Hom sheaves themselves.
In particular the identification `SheafHomComplex.sectionsEquiv` and the morphism `homMap` are
available at the universes of the statement of Stacks 0A90.

Two spellings of one module structure meet here. A section of `K|_U` over an object
`Over.mk f` of the slice site is a section of `K` over the source of `f`, but its scalars are
spelled `(O|_U)(Over.mk f)` in the first case and `O(W)` in the second; the two are
definitionally equal, and only the first is found by instance search, which is why
`sectionsEquiv_smul` states the scalar action at that spelling while
`SheafHomComplex.smul_natural` states it at the other.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe m s u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})

/-- The restriction to the site over `U` of a morphism of cochain complexes of
`O`-modules, formed degreewise. -/
noncomputable abbrev restrictComplexMap (U : X.C)
    {K K' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K ⟶ K') :
    restrictComplex X K U ⟶ restrictComplex X K' U :=
  ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
    (ComplexShape.up ℤ)).map k

/-- The restriction of a morphism of complexes acts degreewise by restriction. -/
lemma restrictComplexMap_f (U : X.C)
    {K K' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K ⟶ K') (p : ℤ) :
    (restrictComplexMap X U k).f p = (k.f p).over U := rfl

section Conj

variable {K K' M M' :
    CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Pre- and postcomposition of a cochain between restricted complexes with the
restrictions of morphisms `k : K' ⟶ K` and `m : M ⟶ M'`. -/
noncomputable def cochainConj (U : X.C) (k : K' ⟶ K) (m : M ⟶ M') {n : ℤ}
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    Cochain (restrictComplex X K' U) (restrictComplex X M' U) n :=
  (Cochain.ofHom (restrictComplexMap X U k)).comp
    (c.comp (Cochain.ofHom (restrictComplexMap X U m)) (add_zero n)) (zero_add n)

/-- The components of `cochainConj`. -/
lemma cochainConj_v (U : X.C) (k : K' ⟶ K) (m : M ⟶ M') {n : ℤ}
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) (p q : ℤ)
    (hpq : p + n = q) :
    (cochainConj X U k m c).v p q hpq =
      (k.f p).over U ≫ c.v p q hpq ≫ (m.f q).over U := by
  rw [cochainConj, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq,
    Cochain.comp_v c _ (add_zero n) p q q hpq (add_zero q), Cochain.ofHom_v,
    Cochain.ofHom_v, restrictComplexMap_f, restrictComplexMap_f]

/-- `cochainConj` is additive. -/
@[simp]
lemma cochainConj_add (U : X.C) (k : K' ⟶ K) (m : M ⟶ M') {n : ℤ}
    (c c' : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainConj X U k m (c + c') = cochainConj X U k m c + cochainConj X U k m c' := by
  ext p q hpq
  simp [cochainConj_v]

/-- `cochainConj` preserves zero. -/
@[simp]
lemma cochainConj_zero (U : X.C) (k : K' ⟶ K) (m : M ⟶ M') (n : ℤ) :
    cochainConj X U k m (0 : Cochain (restrictComplex X K U) (restrictComplex X M U) n) = 0 := by
  ext p q hpq
  simp [cochainConj_v]

/-- Conjugating by the identities does nothing. -/
lemma cochainConj_id (U : X.C) {n : ℤ}
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainConj X U (𝟙 K) (𝟙 M) c = c := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainConj_v]
  have h (L : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (i : ℤ) : ((𝟙 L : L ⟶ L).f i).over U = 𝟙 _ := by
    rw [HomologicalComplex.id_f]
    exact (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_id _
  rw [h, h]
  simp

/-- `cochainConj` commutes with the Hom-complex differential, because it is composition with
morphisms of complexes on either side. -/
lemma cochainConj_δ (U : X.C) (k : K' ⟶ K) (m : M ⟶ M') (n n' : ℤ)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainConj X U k m (δ n n' c) = δ n n' (cochainConj X U k m c) := by
  rw [cochainConj, cochainConj, δ_ofHom_comp, δ_comp_ofHom]

end Conj

/-- Applying a composite of morphisms of sheaves of modules to a section. -/
lemma comp_val_app_apply {C₀ : Type u} [Category.{v} C₀] {J : GrothendieckTopology C₀}
    {R : Sheaf J RingCat.{w}} {A B D : SheafOfModules.{s} R} (φ : A ⟶ B) (ψ : B ⟶ D)
    (W : C₀ᵒᵖ) (x : A.val.obj W) :
    ((φ ≫ ψ).val.app W) x = (ψ.val.app W) ((φ.val.app W) x) := rfl

/-- Evaluating a morphism of sheaves of modules on a fixed section, as an additive map. -/
private noncomputable def evalSectionAddHom {C₀ : Type u} [Category.{v} C₀]
    {J : GrothendieckTopology C₀} {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{s} R}
    (W : C₀ᵒᵖ) (x : A.val.obj W) : (A ⟶ B) →+ B.val.obj W :=
  AddMonoidHom.mk' (fun φ => (φ.val.app W) x) (fun φ ψ => by
    simp only [SheafOfModules.add_val, PresheafOfModules.add_app, ModuleCat.hom_add,
      LinearMap.add_apply])

/-- An integer multiple of a morphism of sheaves of modules acts on sections by the same
multiple. -/
lemma zsmul_val_app_apply {C₀ : Type u} [Category.{v} C₀]
    {J : GrothendieckTopology C₀} {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{s} R}
    (ε : ℤ) (φ : A ⟶ B) (W : C₀ᵒᵖ) (x : A.val.obj W) :
    ((ε • φ).val.app W) x = ε • ((φ.val.app W) x) :=
  map_zsmul (evalSectionAddHom (B := B) W x) ε φ

/-- Restriction of a section of a sheaf of modules along an arrow of the site, with the
type of the restricted section spelled out. -/
noncomputable abbrev restrictSection
    {A : SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {U V : X.C}
    (g : V ⟶ U) (s : A.val.obj (op U)) : A.val.obj (op V) := A.val.map g.op s

/-- Two morphisms of sheaves of modules agree as soon as they agree on all sections. -/
private lemma sheafOfModules_hom_ext_apply {C₀ : Type u} [Category.{v} C₀]
    {J : GrothendieckTopology C₀} {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{s} R}
    {φ ψ : A ⟶ B} (h : ∀ (W : C₀ᵒᵖ) (x : A.val.obj W), (φ.val.app W) x = (ψ.val.app W) x) :
    φ = ψ :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext <| LinearMap.ext (h W)

/-- Two morphisms of sheaves of modules on the site over `U` agree as soon as they agree on
the sections over every object presented as `Over.mk f`. -/
lemma over_hom_ext {U : X.C}
    {A B : SheafOfModules.{s} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)}
    {φ ψ : A ⟶ B}
    (h : ∀ (W : X.C) (f : W ⟶ U) (x : A.val.obj (op (Over.mk f))),
      (φ.val.app (op (Over.mk f))) x = (ψ.val.app (op (Over.mk f))) x) : φ = ψ :=
  sheafOfModules_hom_ext_apply fun V x => h V.unop.left V.unop.hom x

namespace SheafHomComplex

variable {X}
variable {K M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K M)

/-- The description of the sections of the internal Hom complex over `U` in degree `n`,
as an additive equivalence. -/
noncomputable def sectionsEquiv (U : X.C) (n : ℤ) :
    (H.obj.X n).val.obj (op U) ≃+
      Cochain (restrictComplex X K U) (restrictComplex X M U) n :=
  ((HomologicalComplex.eval _ _ n).mapIso (H.sectionsIso U)).addCommGroupIsoToAddEquiv

/-- `sectionsEquiv` is the degree-`n` component of the characterising isomorphism. -/
lemma sectionsEquiv_apply (U : X.C) (n : ℤ) (s : (H.obj.X n).val.obj (op U)) :
    H.sectionsEquiv U n s =
      AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s := rfl

/-- The sections description transports the differential of the internal Hom complex to the
Hom-complex differential `δ`. -/
lemma sectionsEquiv_d (U : X.C) (n n' : ℤ) (s : (H.obj.X n).val.obj (op U)) :
    H.sectionsEquiv U n' ((H.obj.d n n').val.app (op U) s) =
      δ n n' (H.sectionsEquiv U n s) :=
  (ConcreteCategory.congr_hom ((H.sectionsIso U).hom.comm n n') s).symm

/-- `restrict_natural`, in terms of `sectionsEquiv`. -/
lemma sectionsEquiv_restrict {U V : X.C} (g : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) {W : X.C} (h : W ⟶ V)
    (x : ((restrictComplex X K V).X p).val.obj (op (Over.mk h))) :
    ((H.sectionsEquiv V n (restrictSection X g s)).v p q hpq).val.app (op (Over.mk h)) x =
      ((H.sectionsEquiv U n s).v p q hpq).val.app (op (Over.mk (h ≫ g))) x :=
  (H.restrict_natural g n p q hpq s h x).symm

/-- `smul_natural`, in terms of `sectionsEquiv`. -/
lemma sectionsEquiv_smul (U : X.C) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (n p q : ℤ)
    (hpq : p + n = q) (s : (H.obj.X n).val.obj (op U)) {W : X.C} (f : W ⟶ U)
    (x : ((restrictComplex X K U).X p).val.obj (op (Over.mk f))) :
    ((H.sectionsEquiv U n (r • s)).v p q hpq).val.app (op (Over.mk f)) x =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj (op (Over.mk f)) from
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op r) •
        (((H.sectionsEquiv U n s).v p q hpq).val.app (op (Over.mk f)) x) :=
  H.smul_natural U r n p q hpq s f x

/-- `restrict_natural` with the object of the slice site over `V` left as a variable `W` of
`(Over V)ᵒᵖ`, instead of presented as `Over.mk` of an arrow of `C`.

The two forms are definitionally equal, by eta for `Over`, but only this one has the slice object
in the position where a goal over a slice site puts it: there the object of `C/V` is a variable,
and `Over.mk` is not reducibly a constructor application, so the `Over.mk` form of the field does
not rewrite. -/
lemma restrict_natural_app {U V : X.C} (f : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) (W : (Over V)ᵒᵖ)
    (x : ((restrictComplex X K V).X p).val.obj W) :
    (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s).v p q hpq).val.app
        (op (Over.mk (W.unop.hom ≫ f))) x) =
      (((AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n)
        ((H.obj.X n).val.map f.op s)).v p q hpq).val.app W x) :=
  H.restrict_natural f n p q hpq s W.unop.hom x

/-- `smul_natural` with the object of the slice site over `U` left as a variable `W` of
`(Over U)ᵒᵖ`, instead of presented as `Over.mk` of an arrow of `C`. See
`AlgebraicGeometry.RingedSite.SheafHomComplex.restrict_natural_app` for why the two forms are not
interchangeable in a rewrite. -/
lemma smul_natural_app (U : X.C) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (n p q : ℤ)
    (hpq : p + n = q) (s : (H.obj.X n).val.obj (op U)) (W : (Over U)ᵒᵖ)
    (x : ((restrictComplex X K U).X p).val.obj W) :
    (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) (r • s)).v p q hpq).val.app W) x =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj W from
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map W.unop.hom.op r) •
        (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s).v p q hpq).val.app W) x :=
  H.smul_natural U r n p q hpq s W.unop.hom x

end SheafHomComplex

section HomMap

variable {K K' M M' :
    CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The map on sections underlying the morphism of internal Hom complexes induced by
`k : K' ⟶ K` and `m : M ⟶ M'`. -/
noncomputable def homMapFun (k : K' ⟶ K) (m : M ⟶ M') (n : ℤ) (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    ((sheafHomComplex X K' M').obj.X n).val.obj (op U) :=
  ((sheafHomComplex X K' M').sectionsEquiv U n).symm
    (cochainConj X U k m ((sheafHomComplex X K M).sectionsEquiv U n s))

/-- The defining property of `homMapFun`. -/
@[simp]
lemma sectionsEquiv_homMapFun (k : K' ⟶ K) (m : M ⟶ M') (n : ℤ) (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    (sheafHomComplex X K' M').sectionsEquiv U n (homMapFun X k m n U s) =
      cochainConj X U k m ((sheafHomComplex X K M).sectionsEquiv U n s) :=
  ((sheafHomComplex X K' M').sectionsEquiv U n).apply_symm_apply _

/-- The map on sections is additive. -/
lemma homMapFun_add (k : K' ⟶ K) (m : M ⟶ M') (n : ℤ) (U : X.C)
    (s t : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    homMapFun X k m n U (s + t) = homMapFun X k m n U s + homMapFun X k m n U t := by
  apply ((sheafHomComplex X K' M').sectionsEquiv U n).injective
  rw [map_add, sectionsEquiv_homMapFun, sectionsEquiv_homMapFun, sectionsEquiv_homMapFun,
    map_add, cochainConj_add]

/-- The map on sections is linear over the sections of the structure sheaf. -/
lemma homMapFun_smul (k : K' ⟶ K) (m : M ⟶ M') (n : ℤ) (U : X.C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    homMapFun X k m n U (r • s) = r • homMapFun X k m n U s := by
  apply ((sheafHomComplex X K' M').sectionsEquiv U n).injective
  rw [sectionsEquiv_homMapFun]
  refine Cochain.ext _ _ fun p q hpq => over_hom_ext X fun W g x => ?_
  rw [(sheafHomComplex X K' M').sectionsEquiv_smul U r n p q hpq
      (homMapFun X k m n U s) g x, sectionsEquiv_homMapFun, cochainConj_v,
    cochainConj_v, comp_val_app_apply, comp_val_app_apply, comp_val_app_apply,
    comp_val_app_apply, (sheafHomComplex X K M).sectionsEquiv_smul U r n p q hpq s g _]
  exact map_smul _ _ _

/-- The maps on sections are compatible with restriction along arrows of the site. -/
lemma homMapFun_restrict (k : K' ⟶ K) (m : M ⟶ M') (n : ℤ) {U V : X.C} (g : V ⟶ U)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    homMapFun X k m n V (restrictSection X g s) =
      restrictSection X g (homMapFun X k m n U s) := by
  apply ((sheafHomComplex X K' M').sectionsEquiv V n).injective
  rw [sectionsEquiv_homMapFun]
  refine Cochain.ext _ _ fun p q hpq => over_hom_ext X fun W h x => ?_
  rw [cochainConj_v, comp_val_app_apply, comp_val_app_apply,
    (sheafHomComplex X K M).sectionsEquiv_restrict g n p q hpq s h _,
    (sheafHomComplex X K' M').sectionsEquiv_restrict g n p q hpq
      (homMapFun X k m n U s) h x, sectionsEquiv_homMapFun, cochainConj_v]
  rfl

/-- The morphism of internal Hom complexes in degree `n` induced by `k : K' ⟶ K` and
`m : M ⟶ M'`. -/
noncomputable def homMapHom (k : K' ⟶ K) (m : M ⟶ M') (n : ℤ) :
    (sheafHomComplex X K M).obj.X n ⟶ (sheafHomComplex X K' M').obj.X n :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
      { toFun := fun s ↦ homMapFun X k m n U.unop s
        map_add' := fun s t ↦ homMapFun_add X k m n U.unop s t
        map_smul' := fun r s ↦ homMapFun_smul X k m n U.unop r s }
     naturality := by
       rintro ⟨U⟩ ⟨V⟩ ⟨g : V ⟶ U⟩
       exact ModuleCat.hom_ext <| LinearMap.ext fun s => homMapFun_restrict X k m n g s }⟩

/-- The defining property of `homMapHom`. -/
@[simp]
lemma sectionsEquiv_homMapHom (k : K' ⟶ K) (m : M ⟶ M') (n : ℤ) (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    (sheafHomComplex X K' M').sectionsEquiv U n
        ((homMapHom X k m n).val.app (op U) s) =
      cochainConj X U k m ((sheafHomComplex X K M).sectionsEquiv U n s) :=
  sectionsEquiv_homMapFun X k m n U s

/-- The morphism of internal Hom complexes induced by `k : K' ⟶ K` and `m : M ⟶ M'`. -/
noncomputable def homMap (k : K' ⟶ K) (m : M ⟶ M') :
    (sheafHomComplex X K M).obj ⟶ (sheafHomComplex X K' M').obj where
  f n := homMapHom X k m n
  comm' n n' _ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨U⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply ((sheafHomComplex X K' M').sectionsEquiv U n').injective
    rw [comp_val_app_apply, comp_val_app_apply, sectionsEquiv_homMapHom,
      (sheafHomComplex X K M).sectionsEquiv_d, (sheafHomComplex X K' M').sectionsEquiv_d,
      sectionsEquiv_homMapHom, cochainConj_δ]

/-- The degreewise components of `homMap`. -/
@[simp]
lemma homMap_f (k : K' ⟶ K) (m : M ⟶ M') (n : ℤ) :
    (homMap X k m).f n = homMapHom X k m n := rfl

/-- The induced map of internal Hom complexes acts on sections by pre- and
postcomposition. This is part (1) of Stacks 0A90. -/
lemma sectionsIso_homMap_v (k : K' ⟶ K) (m : M ⟶ M') (U : X.C) (n p q : ℤ)
    (hpq : p + n = q) (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    (AddCommGrpCat.Hom.hom
        (((sheafHomComplex X K' M').sectionsIso U).hom.f n)
        (((homMap X k m).f n).val.app (op U) s)).v p q hpq =
      (k.f p).over U ≫
        (AddCommGrpCat.Hom.hom
          (((sheafHomComplex X K M).sectionsIso U).hom.f n) s).v p q hpq ≫
        (m.f q).over U := by
  rw [homMap_f, ← SheafHomComplex.sectionsEquiv_apply, sectionsEquiv_homMapHom,
    cochainConj_v, SheafHomComplex.sectionsEquiv_apply]

/-- The identity maps induce the identity on the internal Hom complex. -/
lemma homMap_id
    (K M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homMap X (𝟙 K) (𝟙 M) = 𝟙 (sheafHomComplex X K M).obj := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine sheafOfModules_hom_ext_apply fun ⟨U⟩ s => ?_
  apply ((sheafHomComplex X K M).sectionsEquiv U n).injective
  rw [homMap_f, sectionsEquiv_homMapHom, cochainConj_id]
  rfl

end HomMap

end AlgebraicGeometry.RingedSite

end
