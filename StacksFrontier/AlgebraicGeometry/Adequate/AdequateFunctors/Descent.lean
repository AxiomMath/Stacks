module

public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Kernels
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Restriction
public import StacksFrontier.Algebra.Module.Adequate.Pushforward
public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of adequate functors

An adequate module-valued functor descends along a ring map when its values form an exact
Čech equalizer for that map.

## Main definitions

* `AdequateFunctor.restrictScalars` restricts commutative algebras along the base ring map.
* `AdequateFunctor.baseAlgebra` regards the target ring as an algebra over the source ring.
* `AdequateFunctor.CechExact` is the Čech condition itself, and
  `AdequateFunctor.cechOnce`, `AdequateFunctor.cechTwice`,
  `AdequateFunctor.cechAugmentation` and `AdequateFunctor.cechDifferential` are the Čech
  diagram whose exactness it asserts.

## Main results

* `AdequateFunctor.isAdequate_of_descent` gives adequacy from adequacy after restriction
  of the base ring and exactness of the Čech sequence.
* `AdequateFunctor.isAdequate_cechOnce`: the degree-one Čech term of an adequate functor is
  adequate, by [Stacks, Tag 06V9] followed by [Stacks, Tag 06VA]. This is the step of the
  descent which supplies the two terms of the Čech equalizer.
* `AdequateFunctor.cechAugmentationKernelIso` exhibits the functor as the kernel of its Čech
  differential under the Čech condition.
* `AdequateFunctor.cechExact_iff_eq` restates the Čech condition with the two faces compared
  by an ordinary equality.

## Implementation notes

The two tensor products in the source are expressed as binary coproducts of commutative
algebras. The equalizer condition is required for every choice of the two coproducts;
this is equivalent to requiring it for their tensor-product models. An isomorphism identifies
the adequate functor over the new base with the restriction of the given functor.

The Čech development is public rather than private, so that a port of the descent to another
domain of algebras -- the algebras of a big site, say, where an affine-section functor lives --
can reuse it instead of re-deriving it. The definitions whose bodies do not survive
`@[expose]`, because they rest on unfolding definitions that are themselves not exposed, are
`@[no_expose] public`.

`AdequateFunctor.baseChangeAdjunction` is *not* among them, and that is load-bearing: the unit
of that adjunction is the Čech map, so without its body a port cannot see that the Čech scalar
comparison and `AdequateFunctor.baseChangeRingHom` are the same map, and
`AdequateFunctor.cechRingMap_eq_baseChangeRingHom` -- the equation a port needs, and the only
step of the port that is not available outside this module -- could not be stated as a public
theorem at all.

## References

* [Stacks Project, Tag 06VH](https://stacks.math.columbia.edu/tag/06VH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe w u

namespace AdequateFunctor


/-- Extension followed by restriction, viewed as an endofunctor on `A`-algebras. -/
public noncomputable abbrev cechBaseChange {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A') : CommAlgCat A ⥤ CommAlgCat A :=
  baseChangeFunctor f ⋙ restrictAlgebras f

/-- Base change along `f` is left adjoint to restriction of the base ring. -/
public noncomputable def baseChangeAdjunction {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A') :
    baseChangeFunctor f ⊣ restrictAlgebras f := by
  let e := commAlgCatEquivUnder (CommRingCat.of A)
  let e' := commAlgCatEquivUnder (CommRingCat.of A')
  let a := e.toAdjunction.comp (Under.mapPushoutAdj (CommRingCat.ofHom f))
  let b := a.comp e'.symm.toAdjunction
  let leftIso :
      (e.functor ⋙ Under.pushout (CommRingCat.ofHom f)) ⋙ e'.inverse ≅
        e.functor ⋙ (Under.pushout (CommRingCat.ofHom f) ⋙ e'.inverse) :=
    Functor.associator _ _ _
  let rightIso : e'.functor ⋙ Under.map (CommRingCat.ofHom f) ⋙ e.inverse ≅
      restrictAlgebras f :=
    NatIso.ofComponents (fun X => by
      let U := (Under.map (CommRingCat.ofHom f)).obj (e'.functor.obj X)
      letI : Algebra A U.right := U.hom.hom.toAlgebra
      letI : Algebra A X := Algebra.compHom X f
      exact CommAlgCat.isoMk
        { toRingEquiv := RingEquiv.refl _, commutes' := by intro a; rfl })
      (by intro X Y g; ext x; rfl)
  exact (b.ofNatIsoLeft leftIso).ofNatIsoRight rightIso

/-- The unit `B ⟶ B ⊗_A A'` of base change, the first map of the Čech diagram. -/
public noncomputable def cechUnit {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A') :
    𝟭 (CommAlgCat A) ⟶ cechBaseChange f :=
  (baseChangeAdjunction f).unit

/-- The unit map into the base-changed algebra. -/
public noncomputable def cechRingMap {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') : algebraRingDiagram A ⟶
      (cechBaseChange f).op.op ⋙ algebraRingDiagram A where
  app X := RingCat.ofHom
    ((cechUnit f).app X.unop.unop).hom.toRingHom
  naturality _ _ g := RingCat.hom_ext <|
    congrArg (fun k => k.hom.toRingHom) ((cechUnit f).naturality g.unop.unop)

/-- The functor `B ↦ F(B ⊗_A A')`, the degree-one term of the Čech diagram of `F`. -/
public noncomputable abbrev cechOnce {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A) :
    ModuleValuedFunctor.{w, u} A :=
  (PresheafOfModules.pushforward (cechRingMap f)).obj F

/-- The functor `B ↦ F(B ⊗_A A' ⊗_A A')`, the degree-two term of the Čech diagram
of `F`. -/
public noncomputable abbrev cechTwice {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A) :
    ModuleValuedFunctor.{w, u} A :=
  (PresheafOfModules.pushforward (cechRingMap f)).obj (cechOnce f F)

/-- The Čech map induced by the unit on the inner factor. -/
public noncomputable def cechMapInner {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A) :
    cechOnce f F ⟶ cechTwice f F where
  app X := (cechOnce f F).map ((cechUnit f).app X.unop.unop).op.op
  naturality := by
    intro X Y g
    ext x
    change (cechOnce f F).map ((cechUnit f).app Y.unop.unop).op.op
        ((cechOnce f F).map g x) =
      (cechOnce f F).map (((cechBaseChange f).op.op).map g)
        ((cechOnce f F).map ((cechUnit f).app X.unop.unop).op.op x)
    have hn := congrArg (fun k => k.op.op) ((cechUnit f).naturality g.unop.unop)
    rw [← (cechOnce f F).map_comp_apply g
      (((cechUnit f).app Y.unop.unop).op.op) x]
    rw [← (cechOnce f F).map_comp_apply (((cechUnit f).app X.unop.unop).op.op)
      (((cechBaseChange f).op.op).map g) x]
    exact (cechOnce f F).congr_map_apply hn x

/-- The augmentation `F ⟶ F(- ⊗_A A')` of the Čech diagram. -/
public noncomputable def cechAugmentation {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A) :
    F ⟶ cechOnce f F where
  app X := F.map ((cechUnit f).app X.unop.unop).op.op
  naturality := by
    intro X Y g
    ext x
    change F.map ((cechUnit f).app Y.unop.unop).op.op (F.map g x) =
      F.map (((cechBaseChange f).op.op).map g)
        (F.map ((cechUnit f).app X.unop.unop).op.op x)
    have hn := congrArg (fun k => k.op.op) ((cechUnit f).naturality g.unop.unop)
    rw [← F.map_comp_apply g (((cechUnit f).app Y.unop.unop).op.op) x]
    rw [← F.map_comp_apply ((cechUnit f).app X.unop.unop).op.op
      (((cechBaseChange f).op.op).map g) x]
    exact F.congr_map_apply hn x

/-- The Čech map induced by the unit on the outer factor. -/
public noncomputable def cechMapOuter {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A) :
    cechOnce f F ⟶ cechTwice f F :=
  (PresheafOfModules.pushforward (cechRingMap f)).map (cechAugmentation f F)

/-- The Čech differential, the difference of the two maps into the degree-two term. -/
public noncomputable def cechDifferential {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A) :
    cechOnce f F ⟶ cechTwice f F := cechMapInner f F - cechMapOuter f F


/-- Restriction of commutative algebras along a ring map. -/
public def restrictScalars {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') : CommAlgCat.{u} A' ⥤ CommAlgCat.{u} A where
  obj B :=
    letI : Algebra A B := Algebra.compHom B f
    CommAlgCat.of A B
  map {B C} g :=
    letI : Algebra A B := Algebra.compHom B f
    letI : Algebra A C := Algebra.compHom C f
    letI : Algebra A A' := f.toAlgebra
    haveI : IsScalarTower A A' B := .of_algebraMap_eq' rfl
    haveI : IsScalarTower A A' C := .of_algebraMap_eq' rfl
    CommAlgCat.ofHom (g.hom.restrictScalars A)

/-- The base ring viewed as an algebra over the original ring. -/
public abbrev baseAlgebra {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') : CommAlgCat.{u} A :=
  letI : Algebra A A' := f.toAlgebra
  CommAlgCat.of A A'

/-- The Čech condition on `F`: its values form an exact equalizer sequence for `f`. -/
public abbrev CechExact {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A) : Prop :=
  ∀ (B B₁ B₂ : CommAlgCat.{u} A)
    (iB : B ⟶ B₁) (iA : baseAlgebra f ⟶ B₁)
    (jB : B₁ ⟶ B₂) (jA : baseAlgebra f ⟶ B₂)
    (q : B₁ ⟶ B₂),
    IsColimit (BinaryCofan.mk iB iA) →
    IsColimit (BinaryCofan.mk jB jA) →
    iB ≫ q = iB ≫ jB → iA ≫ q = jA →
    (Function.Injective (F.map iB.op.op) ∧
      ∀ y : F.obj (Opposite.op (Opposite.op B₁)),
        (HEq (F.map jB.op.op y) (F.map q.op.op y) ↔
          ∃ x : F.obj (Opposite.op (Opposite.op B)),
            F.map iB.op.op x = y))

/-- `AdequateFunctor.CechExact` with the two Čech faces compared by an ordinary equality.

The two faces `jB` and `q` are both morphisms `B₁ ⟶ B₂`, so their values at `y` lie in the same
module and the heterogeneous equality in the definition is an ordinary one. Supplying the Čech
hypothesis of [Stacks, Tag 06VH] -- from the sheaf condition, say -- is easier in this form,
where the equalizer condition is a plain equation between elements of
`F.obj (op (op B₂))`. -/
public theorem cechExact_iff_eq {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A) :
    CechExact f F ↔
      ∀ (B B₁ B₂ : CommAlgCat.{u} A)
        (iB : B ⟶ B₁) (iA : baseAlgebra f ⟶ B₁)
        (jB : B₁ ⟶ B₂) (jA : baseAlgebra f ⟶ B₂)
        (q : B₁ ⟶ B₂),
        IsColimit (BinaryCofan.mk iB iA) →
        IsColimit (BinaryCofan.mk jB jA) →
        iB ≫ q = iB ≫ jB → iA ≫ q = jA →
        (Function.Injective (F.map iB.op.op) ∧
          ∀ y : F.obj (Opposite.op (Opposite.op B₁)),
            (F.map jB.op.op y = F.map q.op.op y ↔
              ∃ x : F.obj (Opposite.op (Opposite.op B)),
                F.map iB.op.op x = y)) := by
  unfold CechExact
  congr! 15
  exact heq_iff_eq

/-- The inclusion of `A'` into `B ⊗_A A'` as an `A`-algebra. -/
public noncomputable def cechBaseInclusion {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (B : CommAlgCat A) :
    baseAlgebra f ⟶ (cechBaseChange f).obj B := by
  let C := (baseChangeFunctor f).obj B
  letI : Algebra A A' := f.toAlgebra
  letI : Algebra A C := Algebra.compHom C f
  haveI : IsScalarTower A A' C := .of_algebraMap_eq' rfl
  exact CommAlgCat.ofHom (IsScalarTower.toAlgHom A A' C)

/-- The inclusion of `A'` into the base change is natural in the algebra. -/
public lemma cechBaseInclusion_naturality {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A')
    {B C : CommAlgCat A} (g : B ⟶ C) :
    cechBaseInclusion f B ≫ (cechBaseChange f).map g = cechBaseInclusion f C := by
  let : Algebra A A' := f.toAlgebra
  let : Algebra A ((baseChangeFunctor f).obj B) :=
    Algebra.compHom ((baseChangeFunctor f).obj B) f
  let : Algebra A ((baseChangeFunctor f).obj C) :=
    Algebra.compHom ((baseChangeFunctor f).obj C) f
  have : IsScalarTower A A' ((baseChangeFunctor f).obj B) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower A A' ((baseChangeFunctor f).obj C) :=
    .of_algebraMap_eq' rfl
  refine CommAlgCat.hom_ext (AlgHom.ext fun a => ?_)
  change ((baseChangeFunctor f).map g).hom
      (algebraMap A' ((baseChangeFunctor f).obj B) a) =
    algebraMap A' ((baseChangeFunctor f).obj C) a
  exact ((baseChangeFunctor f).map g).hom.commutes a

/-- The degree-one Čech term of `F` is the pushforward of an `A'`-algebra functor identified
with the restriction of `F`. -/
@[no_expose] public noncomputable def cechOnceIsoPushforward {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A')
    (F : ModuleValuedFunctor.{w, u} A)
    (F' : ModuleValuedFunctor.{w, u} A')
    (e : F' ≅ (PresheafOfModules.pushforward₀ (restrictScalars f).op
      (algebraRingDiagram A)).obj F) :
    cechOnce f F ≅ pushforward f F' := by
  refine PresheafOfModules.isoMk (fun X => ?_) (fun {X Y} g => ?_)
  · let C := (baseChangeFunctor f).obj X.unop.unop
    let Cidx := (baseChangeFunctor f).op.op.obj X
    have he' : ((PresheafOfModules.pushforward₀ (restrictScalars f).op
        (algebraRingDiagram A)).obj F).obj Cidx ≅ F'.obj Cidx := by
      refine ⟨e.inv.app Cidx, e.hom.app Cidx, ?_, ?_⟩
      · change e.inv.app Cidx ≫ e.hom.app Cidx = 𝟙 _
        exact congrArg (fun k => k.app Cidx) e.inv_hom_id
      · change e.hom.app Cidx ≫ e.inv.app Cidx = 𝟙 _
        exact congrArg (fun k => k.app Cidx) e.hom_inv_id
    have hobj : (restrictScalars f).obj C =
        (restrictAlgebras f).obj C := rfl
    have he : F.obj ((cechBaseChange f).op.op.obj X) ≅
        F'.obj Cidx := by
      have heq : F.obj (Opposite.op (Opposite.op ((restrictScalars f).obj C))) ≅
          F.obj (Opposite.op (Opposite.op ((restrictAlgebras f).obj C))) := by
        cases hobj
        exact Iso.refl _
      change F.obj (Opposite.op (Opposite.op ((restrictAlgebras f).obj C))) ≅
        F'.obj Cidx
      exact heq.symm ≪≫ he'
    change (ModuleCat.restrictScalars ((cechRingMap f).app X).hom).obj
        (F.obj ((cechBaseChange f).op.op.obj X)) ≅
      (ModuleCat.restrictScalars ((baseChangeRingHom f).app X).hom).obj
        (F'.obj ((baseChangeFunctor f).op.op.obj X))
    exact (ModuleCat.restrictScalars ((cechRingMap f).app X).hom).mapIso he
  · ext x
    exact PresheafOfModules.naturality_apply e.inv
      (((baseChangeFunctor f).op.op).map g) x

/-- The pushforward of `F` along restriction of algebras agrees with the restriction functor
applied to `F`. -/
@[no_expose] public noncomputable def restrictFunctorIsoPushforwardZero {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A')
    (F : ModuleValuedFunctor.{w, u} A) :
    (PresheafOfModules.pushforward₀ (restrictScalars f).op
      (algebraRingDiagram A)).obj F ≅
      (restrictFunctor f).obj F := by
  refine PresheafOfModules.isoMk (fun X => ?_) ?_
  · let C := X.unop.unop
    let B := (restrictAlgebras f).obj C
    have hB : (restrictScalars f).obj C = B := rfl
    let M := F.obj (Opposite.op (Opposite.op B))
    have hM : F.obj (Opposite.op (Opposite.op ((restrictScalars f).obj C))) = M :=
      by cases hB; rfl
    change (F.obj (Opposite.op (Opposite.op ((restrictScalars f).obj C))) :
        ModuleCat ((algebraRingDiagram A').obj X)) ≅
      (ModuleCat.restrictScalars ((restrictRingDiagram f).app X).hom).obj
        (F.obj (Opposite.op (Opposite.op B)))
    rw [hM]
    exact (ModuleCat.restrictScalarsId'App
      ((restrictRingDiagram f).app X).hom rfl M).symm
  · intro X Y g
    ext x
    rfl

/-- The cofan exhibiting `B ⊗_A A'` as a binary coproduct of `B` and `A'` in `A`-algebras. -/
public noncomputable def cechCofan {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (B : CommAlgCat A) : BinaryCofan B (baseAlgebra f) :=
  BinaryCofan.mk (P := (cechBaseChange f).obj B)
    ((cechUnit f).app B) (cechBaseInclusion f B)

/-- The algebra map out of `B ⊗_A A'` determined by maps out of `B` and out of `A'`. -/
private noncomputable def cechDesc {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (B : CommAlgCat A) {T : CommAlgCat A}
    (iB : B ⟶ T) (iA : baseAlgebra f ⟶ T) :
    (cechCofan f B).pt ⟶ T := by
  let e := commAlgCatEquivUnder (CommRingCat.of A)
  let b := e.functor.obj B
  let a := e.functor.obj (baseAlgebra f)
  let pt := (Under.map (CommRingCat.ofHom f)).obj
    ((Under.pushout (CommRingCat.ofHom f)).obj b)
  let hb := e.functor.map iB
  let ha := e.functor.map iA
  let d := pushout.desc hb.right ha.right (hb.w.trans ha.w.symm)
  have hd' : pt.hom ≫ d = (e.functor.obj T).hom := by
    change (a.hom ≫ pushout.inr b.hom a.hom) ≫ d = _
    rw [Category.assoc, pushout.inr_desc]
    exact ha.w
  have hd : pt ⟶ e.functor.obj T := Under.homMk d hd'
  exact e.inverse.map hd ≫ e.unitIso.inv.app T

/-- `AdequateFunctor.cechDesc` is the pushout description map, read in the category of
commutative rings over `A`. -/
private lemma cechDesc_right {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (B : CommAlgCat A) {T : CommAlgCat A}
    (iB : B ⟶ T) (iA : baseAlgebra f ⟶ T) :
    Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
      (cechDesc f B iB iA)) =
      pushout.desc
        (Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map iB))
        (Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map iA))
        (((commAlgCatEquivUnder (CommRingCat.of A)).functor.map iB).w.trans
          ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map iA).w.symm) := by
  ext x
  dsimp [cechDesc, commAlgCatEquivUnder]
  rfl

/-- `AdequateFunctor.cechDesc` restricts along the first coproduct inclusion to the given map
out of `B`. -/
private lemma cechDesc_inl_fac {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (B : CommAlgCat A) {T : CommAlgCat A}
    (iB : B ⟶ T) (iA : baseAlgebra f ⟶ T) :
    pushout.inl ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B).hom
        (CommRingCat.ofHom f) ≫
      Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
        (cechDesc f B iB iA)) =
      Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map iB) := by
  rw [cechDesc_right]
  exact pushout.inl_desc _ _ _

/-- `AdequateFunctor.cechDesc` restricts along the second coproduct inclusion to the given map
out of `A'`. -/
private lemma cechDesc_inr_fac {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (B : CommAlgCat A) {T : CommAlgCat A}
    (iB : B ⟶ T) (iA : baseAlgebra f ⟶ T) :
    pushout.inr ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B).hom
        (CommRingCat.ofHom f) ≫
      Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
        (cechDesc f B iB iA)) =
      Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map iA) := by
  rw [cechDesc_right]
  exact pushout.inr_desc _ _ _

/-- The Čech unit is the first pushout inclusion, read in commutative rings over `A`. -/
private lemma cechUnit_right {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (B : CommAlgCat A) :
    Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
      ((cechUnit f).app B)) =
      pushout.inl ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B).hom
        (CommRingCat.ofHom f) := by
  ext x
  simp [cechUnit, cechBaseChange, commAlgCatEquivUnder]
  rfl

/-- The inclusion of `A'` is the second pushout inclusion, read in commutative rings
over `A`. -/
private lemma cechBaseInclusion_right {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A') (B : CommAlgCat A) :
    Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
      (cechBaseInclusion f B)) =
      pushout.inr ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B).hom
        (CommRingCat.ofHom f) := by
  ext x
  simp [cechBaseInclusion, cechBaseChange, commAlgCatEquivUnder]
  rfl

/-- `AdequateFunctor.cechCofan` is a coproduct: the base change is the pushout of `B` and `A'`
over `A`. -/
@[no_expose] public noncomputable def cechCofanIsColimit {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A') (B : CommAlgCat A) :
    IsColimit (cechCofan f B) := by
  refine BinaryCofan.IsColimit.mk (cechCofan f B)
    (fun iB iA => cechDesc f B iB iA) ?_ ?_ ?_
  · intro T iB iA
    apply (commAlgCatEquivUnder (CommRingCat.of A)).functor.map_injective
    apply Under.UnderMorphism.ext
    rw [(commAlgCatEquivUnder (CommRingCat.of A)).functor.map_comp]
    change Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
        ((cechUnit f).app B)) ≫
      Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
        (cechDesc f B iB iA)) = _
    rw [cechUnit_right]
    exact cechDesc_inl_fac f B iB iA
  · intro T iB iA
    apply (commAlgCatEquivUnder (CommRingCat.of A)).functor.map_injective
    apply Under.UnderMorphism.ext
    rw [(commAlgCatEquivUnder (CommRingCat.of A)).functor.map_comp]
    change Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
        (cechBaseInclusion f B)) ≫
      Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
        (cechDesc f B iB iA)) = _
    rw [cechBaseInclusion_right]
    exact cechDesc_inr_fac f B iB iA
  · intro T iB iA m hmB hmA
    apply (commAlgCatEquivUnder (CommRingCat.of A)).functor.map_injective
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · have h := congrArg (fun k => Under.Hom.right
        ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map k)) hmB
      rw [(commAlgCatEquivUnder (CommRingCat.of A)).functor.map_comp] at h
      change Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
          ((cechUnit f).app B)) ≫
        Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map m) = _ at h
      rw [cechUnit_right] at h
      exact h.trans (cechDesc_inl_fac f B iB iA).symm
    · have h := congrArg (fun k => Under.Hom.right
        ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map k)) hmA
      rw [(commAlgCatEquivUnder (CommRingCat.of A)).functor.map_comp] at h
      change Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map
          (cechBaseInclusion f B)) ≫
        Under.Hom.right ((commAlgCatEquivUnder (CommRingCat.of A)).functor.map m) = _ at h
      rw [cechBaseInclusion_right] at h
      exact h.trans (cechDesc_inr_fac f B iB iA).symm

/-- The Čech condition, read at a single algebra: the augmentation is injective and a section
killed by the differential comes from the base. -/
private lemma cechExactAt {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A)
    (hexact : CechExact f F)
    (B : CommAlgCat A) :
    Function.Injective (F.map ((cechUnit f).app B).op.op) ∧
      ∀ y : F.obj (Opposite.op (Opposite.op ((cechBaseChange f).obj B))),
        (HEq (F.map ((cechUnit f).app ((cechBaseChange f).obj B)).op.op y)
            (F.map ((cechBaseChange f).map ((cechUnit f).app B)).op.op y) ↔
          ∃ x : F.obj (Opposite.op (Opposite.op B)),
            F.map ((cechUnit f).app B).op.op x = y) := by
  let B₁ := (cechBaseChange f).obj B
  let B₂ := (cechBaseChange f).obj B₁
  let iB := (cechUnit f).app B
  let iA := cechBaseInclusion f B
  let jB := (cechUnit f).app B₁
  let jA := cechBaseInclusion f B₁
  let q := (cechBaseChange f).map iB
  simpa [B₁, B₂, iB, iA, jB, jA, q] using
    hexact B B₁ B₂ iB iA jB jA q (cechCofanIsColimit f B) (cechCofanIsColimit f B₁)
      ((cechUnit f).naturality ((cechUnit f).app B)).symm
      (cechBaseInclusion_naturality f ((cechUnit f).app B))

/-- A section is killed by the Čech differential exactly when its two images in the
degree-two term agree. -/
private lemma cechDifferential_app_eq_iff {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A')
    (F : ModuleValuedFunctor.{w, u} A)
    (B : CommAlgCat A) (y : F.obj (Opposite.op (Opposite.op ((cechBaseChange f).obj B)))) :
    (cechDifferential f F).app (Opposite.op (Opposite.op B)) y = 0 ↔
      HEq (F.map ((cechUnit f).app ((cechBaseChange f).obj B)).op.op y)
        (F.map ((cechBaseChange f).map ((cechUnit f).app B)).op.op y) := by
  change ((cechMapInner f F).app (Opposite.op (Opposite.op B)) y -
      (cechMapOuter f F).app (Opposite.op (Opposite.op B)) y) = 0 ↔
    HEq ((cechMapOuter f F).app (Opposite.op (Opposite.op B)) y)
      ((cechMapInner f F).app (Opposite.op (Opposite.op B)) y)
  exact sub_eq_zero.trans ⟨fun h => heq_of_eq h.symm, fun h => (eq_of_heq h).symm⟩

/-- The Čech condition gives exactness of the augmentation followed by the differential at a
single algebra. -/
public lemma cechPointExactAt {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A)
    (hexact : CechExact f F)
    (B : CommAlgCat A) :
    Function.Exact
      (((cechAugmentation f F).app (Opposite.op (Opposite.op B))).hom)
      (((cechDifferential f F).app (Opposite.op (Opposite.op B))).hom) ∧
    Function.Injective
      (((cechAugmentation f F).app (Opposite.op (Opposite.op B))).hom) := by
  have h := cechExactAt f F hexact B
  refine ⟨fun y => ⟨fun hy => (h.2 y).1 ((cechDifferential_app_eq_iff f F B y).1 hy), ?_⟩, h.1⟩
  rintro ⟨x, rfl⟩
  exact (cechDifferential_app_eq_iff f F B (F.map ((cechUnit f).app B).op.op x)).2
    ((h.2 _).2 ⟨x, rfl⟩)

/-- The augmentation composed with the Čech differential is zero. -/
public lemma cechAugmentation_comp_differential {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A')
    (F : ModuleValuedFunctor.{w, u} A)
    (hexact : CechExact f F) :
    cechAugmentation f F ≫ cechDifferential f F = 0 := by
  ext X x
  change (((cechDifferential f F).app X).hom
    (((cechAugmentation f F).app X).hom x)) = 0
  exact (cechPointExactAt f F hexact X.unop.unop).1.apply_apply_eq_zero x

/-- Under the Čech condition the augmentation exhibits `F` as the kernel of the Čech
differential. -/
public noncomputable def cechAugmentationKernelIsLimit {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A')
    (F : ModuleValuedFunctor.{w, u} A)
    (hexact : CechExact f F) :
    IsLimit (KernelFork.ofι (cechAugmentation f F)
      (cechAugmentation_comp_differential f F hexact)) := by
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro X
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (cechAugmentation f F)
      (cechAugmentation_comp_differential f F hexact))
    (PresheafOfModules.evaluation (algebraRingDiagram A) X)).symm
    (ModuleCat.isLimitKernelFork
    ((cechAugmentation f F).app X) ((cechDifferential f F).app X)
    (cechPointExactAt f F hexact X.unop.unop).1
    (cechPointExactAt f F hexact X.unop.unop).2)

/-- Under the Čech condition `F` is the kernel of its Čech differential. -/
public noncomputable def cechAugmentationKernelIso {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A')
    (F : ModuleValuedFunctor.{w, u} A)
    (hexact : CechExact f F) :
    F ≅ kernel (cechDifferential f F) :=
  (cechAugmentationKernelIsLimit f F hexact).conePointUniqueUpToIso
    (limit.isLimit (parallelPair (cechDifferential f F) 0))

/-- The degree-one Čech term of an adequate module-valued functor is again adequate: it is the
pushforward along `f` of the restriction of the functor to `A'`-algebras, which is adequate by
[Stacks, Tag 06V9], and pushforward preserves adequacy by [Stacks, Tag 06VA]. Applied to
`AdequateFunctor.cechOnce` itself this gives adequacy of `AdequateFunctor.cechTwice`. -/
public lemma isAdequate_cechOnce {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A')
    (F : ModuleValuedFunctor.{w, u} A)
    (hF : IsAdequate.{w, u} (𝟭 _) F) :
    IsAdequate.{w, u} (𝟭 _) (cechOnce f F) := by
  have hRestrict : IsAdequate.{w, u} (𝟭 _) ((restrictFunctor.{w, u} f).obj F) := by
    obtain ⟨M, N, g, ⟨e⟩⟩ := IsAdequate.restrict.{w, u} f F hF
    exact ⟨M, N, g,
      ⟨(presheafOfModulesUliftIso.{u, w}
        (algebraRingDiagram A') _).symm ≪≫ e⟩⟩
  exact (isAdequate_pushforward f ((restrictFunctor.{w, u} f).obj F) hRestrict).of_iso
    (cechOnceIsoPushforward f F ((restrictFunctor.{w, u} f).obj F)
      (restrictFunctorIsoPushforwardZero f F).symm)

/-- Adequacy descends through an exact Čech equalizer. -/
@[stacks 06VH]
public theorem isAdequate_of_descent {A A' : Type u}
    [CommRing A] [CommRing A'] (f : A →+* A')
    (F : ModuleValuedFunctor.{w, u} A)
    (F' : ModuleValuedFunctor.{w, u} A')
    (hF' : IsAdequate (𝟭 _) F')
    (hrestrict : Nonempty
      (F' ≅ (PresheafOfModules.pushforward₀ (restrictScalars f).op
        (algebraRingDiagram A)).obj F))
    (hexact : CechExact f F) :
    IsAdequate (𝟭 _) F := by
  rcases hrestrict with ⟨e⟩
  have hOnce : IsAdequate (𝟭 _) (cechOnce f F) :=
    (isAdequate_pushforward f F' hF').of_iso
      (cechOnceIsoPushforward f F F' e)
  have hTwice : IsAdequate (𝟭 _) (cechTwice f F) :=
    isAdequate_cechOnce f (cechOnce f F) hOnce
  exact (isAdequate_kernel (cechDifferential f F) hOnce hTwice).of_iso
    (cechAugmentationKernelIso f F hexact)


/-- The scalar comparison of the Čech diagram is the injection into the pushout: the unit of
base change, `AdequateFunctor.cechRingMap`, and `AdequateFunctor.baseChangeRingHom` are one and
the same map of ring diagrams.

Stated because it is the one step of a port of the Čech development to another domain of
algebras that is not available outside this module: it holds by `rfl`, but only through the
body of `AdequateFunctor.baseChangeAdjunction`, whose unit `AdequateFunctor.cechUnit` is. -/
public theorem cechRingMap_eq_baseChangeRingHom {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') : cechRingMap f = baseChangeRingHom f := rfl

end AdequateFunctor
