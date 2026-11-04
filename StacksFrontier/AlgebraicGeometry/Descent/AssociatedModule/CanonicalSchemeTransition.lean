module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiTransitionExists
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData

/-!
# The transition of the canonical descent datum, in the category of modules on the test scheme

The comparison isomorphisms of `AlgebraicGeometry.modulePullbackPseudofunctor` and the transitions
of the canonical descent datum of Stacks 04W5, restated in `AlgebraicGeometry.Scheme.Modules` and
written out through `AlgebraicGeometry.Scheme.Modules.pullbackComp`.

## Main definitions

* `AlgebraicGeometry.modulesPullbackFactorIso`: the pullback along a composite is the iterated
  pullback.
* `AlgebraicGeometry.modulesCanonicalTransition`: the transition of the canonical descent datum
  of a quasi-coherent module over a scheme, at a test scheme mapping to two members of the
  family.

## Main results

* `AlgebraicGeometry.modulesPullbackFactorIso_eq`: it is the transport along the factorization
  followed by the inverse of `AlgebraicGeometry.Scheme.Modules.pullbackComp`.
* `AlgebraicGeometry.modulesCanonicalTransition_eq`: the transition is
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` below the first pair, the transport along the
  equality of the two composites, and the inverse of the comparison below the second pair.
* `AlgebraicGeometry.pullback_map_eqToHom` and `AlgebraicGeometry.pullbackComp_conj_eq`: the
  transition in that spelling at two modules identified by an isomorphism of the target is the
  conjugate of the transition at the other, by the iterated pullbacks of that isomorphism.
* `AlgebraicGeometry.restrictDescentDataHom_comm_modules`: the compatibility square of a
  morphism of descent data for the restricted pullback pseudofunctor, read in
  `AlgebraicGeometry.Scheme.Modules`.
* `AlgebraicGeometry.restrictDescentDataObj_hom_canonical`: the restricted canonical descent
  datum over schemes has `AlgebraicGeometry.modulesCanonicalTransition` for its transitions.
* `Stacks.conj_of_two_squares`: the conjugation of two commuting squares joined by a third.

## Implementation notes

The `CategoryTheory.Cat`-bundled category `AlgebraicGeometry.modulePullbackPseudofunctor.obj
(.mk (op V))` and `AlgebraicGeometry.Scheme.Modules` are definitionally equal but different
terms, so a composite with one factor in each is not matched by `CategoryTheory.Category.assoc`.
The declarations here are ascribed to `AlgebraicGeometry.Scheme.Modules`, and
`AlgebraicGeometry.restrictDescentDataHom_comm_modules` is stated at a variable base functor and
family.

## References

* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t u

namespace AlgebraicGeometry

/-- The pullback of `M` along a composite `g ≫ p` is the pullback along `g` of its pullback along
`p`, as an isomorphism in `AlgebraicGeometry.Scheme.Modules`. -/
def modulesPullbackFactorIso {Y' Y Z : Scheme.{u}} (p : Y ⟶ Z) (g : Y' ⟶ Y) (gp : Y' ⟶ Z)
    (h : g ≫ p = gp) (M : Z.Modules) :
    (Scheme.Modules.pullback gp).obj M ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback p).obj M) :=
  pullModComp g p gp h M

/-- `AlgebraicGeometry.modulesPullbackFactorIso` is the transport along the factorization followed
by the inverse of `AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
theorem modulesPullbackFactorIso_eq {Y' Y Z : Scheme.{u}} (p : Y ⟶ Z) (g : Y' ⟶ Y)
    (gp : Y' ⟶ Z) (h : g ≫ p = gp) (M : Z.Modules) :
    modulesPullbackFactorIso p g gp h M =
      eqToIso (congrArg (fun m : Y' ⟶ Z => (Scheme.Modules.pullback m).obj M) h).symm ≪≫
        ((Scheme.Modules.pullbackComp g p).app M).symm := by
  subst h
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToHom_refl, Category.id_comp]
  rfl

variable {Iw : Type t} {S : Scheme.{u}} {Y : Iw → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
  (W : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
  {V : Scheme.{u}} (q : V ⟶ S) (i j : Iw) (f₁ : V ⟶ Y i) (f₂ : V ⟶ Y j)
  (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q)

/-- The transition of the canonical descent datum of a quasi-coherent module `W`, in the category
of modules on the test scheme: over a scheme `V` mapping to the `i`-th and `j`-th members of the
family with equal composites to the base, it compares the two iterated pullbacks of `W`. -/
def modulesCanonicalTransition :
    (Scheme.Modules.pullback f₁).obj ((Scheme.Modules.pullback (f i)).obj W.obj) ⟶
      (Scheme.Modules.pullback f₂).obj ((Scheme.Modules.pullback (f j)).obj W.obj) :=
  (((canonicalDescentFunctor f).obj W).obj).hom q f₁ f₂ h₁ h₂

/-- The transition of the canonical descent datum is the comparison
`AlgebraicGeometry.Scheme.Modules.pullbackComp` below the first pair of morphisms, the transport
along the equality of the two composites, and the inverse of the comparison below the second
pair. -/
theorem modulesCanonicalTransition_eq :
    modulesCanonicalTransition f W q i j f₁ f₂ h₁ h₂ =
      ((Scheme.Modules.pullbackComp f₁ (f i)).app W.obj).hom ≫
        eqToHom (congrArg (fun m : V ⟶ S => (Scheme.Modules.pullback m).obj W.obj)
          (h₁.trans h₂.symm)) ≫
        ((Scheme.Modules.pullbackComp f₂ (f j)).app W.obj).inv := by
  have key : modulesCanonicalTransition f W q i j f₁ f₂ h₁ h₂ =
      (modulesPullbackFactorIso (f i) f₁ q h₁ W.obj).inv ≫
        (modulesPullbackFactorIso (f j) f₂ q h₂ W.obj).hom :=
    canonicalDescentFunctor_obj_obj_hom f W q i j f₁ f₂ h₁ h₂
  rw [key, modulesPullbackFactorIso_eq (f i) f₁ q h₁ W.obj,
    modulesPullbackFactorIso_eq (f j) f₂ q h₂ W.obj]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans_assoc]

/-! ### The canonical transition at two isomorphic modules -/

section Conjugate

/-- Transporting the pullback of a morphism of modules along an equality of morphisms of
schemes. -/
public theorem pullback_map_eqToHom {Z Wt : Scheme.{u}} {m m' : Z ⟶ Wt} (h : m = m')
    {X Y : Wt.Modules} (χ : X ⟶ Y) :
    (Scheme.Modules.pullback m).map χ ≫
        eqToHom (congrArg (fun z : Z ⟶ Wt => (Scheme.Modules.pullback z).obj Y) h) =
      eqToHom (congrArg (fun z : Z ⟶ Wt => (Scheme.Modules.pullback z).obj X) h) ≫
        (Scheme.Modules.pullback m').map χ := by
  subst h
  simp

/-- For two factorizations `a ≫ p = b ≫ r` of one morphism of schemes and an isomorphism
`χ : X ≅ Y` of modules on the target, the composite of the two comparisons of iterated pullbacks
and the transport along the equality at `Y`, conjugated by the iterated pullbacks of `χ`, is the
same composite at `X`. -/
public theorem pullbackComp_conj_eq {Z V₁ V₂ Wt : Scheme.{u}} (a : Z ⟶ V₁) (p : V₁ ⟶ Wt)
    (b : Z ⟶ V₂) (r : V₂ ⟶ Wt) (h : a ≫ p = b ≫ r) {X Y : Wt.Modules} (χ : X ≅ Y) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback p).map χ.hom) ≫
        (((Scheme.Modules.pullbackComp a p).app Y).hom ≫
          eqToHom (congrArg (fun z : Z ⟶ Wt => (Scheme.Modules.pullback z).obj Y) h) ≫
          ((Scheme.Modules.pullbackComp b r).app Y).inv) ≫
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback r).map χ.inv) =
      ((Scheme.Modules.pullbackComp a p).app X).hom ≫
        eqToHom (congrArg (fun z : Z ⟶ Wt => (Scheme.Modules.pullback z).obj X) h) ≫
        ((Scheme.Modules.pullbackComp b r).app X).inv := by
  have hA : (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback p).map χ.hom) ≫
      ((Scheme.Modules.pullbackComp a p).app Y).hom =
      ((Scheme.Modules.pullbackComp a p).app X).hom ≫
        (Scheme.Modules.pullback (a ≫ p)).map χ.hom :=
    (Scheme.Modules.pullbackComp a p).hom.naturality χ.hom
  have hB' : (Scheme.Modules.pullback (b ≫ r)).map χ.hom ≫
      ((Scheme.Modules.pullbackComp b r).app Y).inv =
      ((Scheme.Modules.pullbackComp b r).app X).inv ≫
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback r).map χ.hom) :=
    (Scheme.Modules.pullbackComp b r).inv.naturality χ.hom
  have heq := pullback_map_eqToHom (X := X) (Y := Y) h χ.hom
  have hmap : (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback r).map χ.hom) ≫
      (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback r).map χ.inv) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, χ.hom_inv_id]
    simp
  simp only [Category.assoc]
  rw [reassoc_of% hA, reassoc_of% heq, reassoc_of% hB', hmap, Category.comp_id]

end Conjugate

/-! ### The compatibility square of a morphism of restricted descent data -/

section Restrict

variable {C' : Type*} [CategoryTheory.Category C'] (ι : C' ⥤ Scheme.{u})
  {Iw : Type t} {Sb : C'} {Xb : Iw → C'} (g : ∀ i, Xb i ⟶ Sb)

/-- The compatibility square of a morphism of descent data for the restricted pullback
pseudofunctor, read in the category of modules on the test object's scheme: over an object `Y`
of `C'` mapping to the `i`-th and `j`-th members of the family with equal composites to the base,
the inverse image of the `i`-th component morphism commutes with the two transitions. -/
public theorem restrictDescentDataHom_comm_modules
    {D E : (modulePullbackPseudofunctor.restrict ι).DescentData g} (φ : D ⟶ E)
    {Y : C'} (q : Y ⟶ Sb) {i j : Iw} (a : Y ⟶ Xb i) (b : Y ⟶ Xb j)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q) :
    (Scheme.Modules.pullback (ι.map a)).map (φ.hom i) ≫ E.hom q a b ha hb =
      D.hom q a b ha hb ≫ (Scheme.Modules.pullback (ι.map b)).map (φ.hom j) :=
  φ.comm q a b ha hb

/-- The transitions of the canonical descent datum over schemes, restricted along `ι`, are
`AlgebraicGeometry.modulesCanonicalTransition`. -/
public theorem restrictDescentDataObj_hom_canonical
    (W : (SheafOfModules.isQuasicoherent (ι.obj Sb).ringCatSheaf).FullSubcategory)
    (Y : C') (q : Y ⟶ Sb) (i j : Iw) (a : Y ⟶ Xb i) (b : Y ⟶ Xb j)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q)
    (ha' : ι.map a ≫ ι.map (g i) = ι.map q) (hb' : ι.map b ≫ ι.map (g j) = ι.map q) :
    (Pseudofunctor.restrictDescentDataObj modulePullbackPseudofunctor ι g
          ((canonicalDescentFunctor fun i => ι.map (g i)).obj W).obj).hom q a b ha hb =
      modulesCanonicalTransition (fun i => ι.map (g i)) W (ι.map q) i j (ι.map a) (ι.map b)
        ha' hb' :=
  Pseudofunctor.restrictDescentDataObj_hom modulePullbackPseudofunctor ι g _ Y q i j a b ha hb

end Restrict

end AlgebraicGeometry

namespace Stacks

/-- If the isomorphism `zE` is the transition `PaN ≫ eN ≫ PbN.inv` conjugated by `Ki`, `Kj`
(`hcan`), the isomorphism `zD` is the transition `PaM ≫ eM ≫ PbM.inv` conjugated by `Li`, `Lj`
(`hstep`), and `Gi`, `Gj` carry the second transition to the first (`hnat`), then `zE` and `zD`
are conjugate by the two composites `Ki.symm ≪≫ Gi ≪≫ Li` and `Kj.symm ≪≫ Gj ≪≫ Lj`. -/
public theorem conj_of_two_squares {C₀ : Type*} [CategoryTheory.Category C₀]
    {XA XB A Bb YA YB A' Bb' TN TN' TM TM' : C₀}
    (Ki : XA ≅ A) (Kj : XB ≅ Bb) (Gi : XA ≅ YA) (Gj : XB ≅ YB) (Li : YA ≅ A') (Lj : YB ≅ Bb')
    (zE : A ≅ Bb) (zD : A' ≅ Bb')
    (PaN : XA ⟶ TN) (eN : TN ⟶ TN') (PbN : XB ≅ TN')
    (PaM : YA ⟶ TM) (eM : TM ⟶ TM') (PbM : YB ≅ TM')
    (hcan : Ki.hom ≫ zE.hom = PaN ≫ eN ≫ PbN.inv ≫ Kj.hom)
    (hstep : Li.hom ≫ zD.hom = (PaM ≫ eM ≫ PbM.inv) ≫ Lj.hom)
    (hnat : Gi.hom ≫ (PaM ≫ eM ≫ PbM.inv) ≫ Gj.inv = PaN ≫ eN ≫ PbN.inv) :
    (Ki.symm ≪≫ Gi ≪≫ Li).inv ≫ zE.hom = zD.hom ≫ (Kj.symm ≪≫ Gj ≪≫ Lj).inv := by
  have hzE : zE.hom = Ki.inv ≫ (PaN ≫ eN ≫ PbN.inv) ≫ Kj.hom := by
    rw [CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, ← hcan,
      CategoryTheory.Iso.inv_hom_id_assoc]
  have hzD : zD.hom = Li.inv ≫ (PaM ≫ eM ≫ PbM.inv) ≫ Lj.hom := by
    rw [← hstep, CategoryTheory.Iso.inv_hom_id_assoc]
  rw [hzD, hzE, ← hnat]
  simp only [Iso.trans_inv, Iso.symm_inv, CategoryTheory.Category.assoc,
    CategoryTheory.Iso.inv_hom_id_assoc, CategoryTheory.Iso.hom_inv_id_assoc]

end Stacks

end
