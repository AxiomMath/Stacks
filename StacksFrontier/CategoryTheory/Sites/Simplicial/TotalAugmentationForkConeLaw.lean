module

public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousCompCoherence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkInverseImage

/-!
# The cone law of the total augmentation of a cocontinuous simplicial site

Let `C` be a simplicial family of sites whose transition functors are cocontinuous and let `a`
be an augmentation of `C` towards a site `(D, K)`. The augmentation of the total site is the
morphism of topoi induced by the cocontinuous functor out of the total category, and its direct
image carries, in each simplicial degree, a canonical map to the direct image of the
augmentation of that degree. Stacks 0D70 (3) asserts that those maps form a cone over the
transitions of the component direct images; this file proves that cone law, unconditionally,
for every sheaf on the total site and every map of simplices.

## Main definitions

* `ranOpMap`: the map of right Kan extensions induced by a natural transformation of the two
  functors extended along, obtained by conjugating the corresponding transformation of the
  precomposition functors.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.transitionSiteFunctor`,
  `.vertexSiteFunctor`, `.augSiteFunctor` and `.totalSiteFunctor`: the four site functors of the
  situation.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.fibreInclusionTransition`: the
  cross-fibre arrows of the total category.

## Main results

* `ranOpCompIso_ranOpMap`: for a natural transformation `ν` of two functors into a common target,
  and a third functor `u` out of that target, if the whiskering of `ν` with `u` is the transport
  along an equality of the two composites, then the square formed by the map of right Kan
  extensions induced by `ν`, the two compositors and the transport of right Kan extensions along
  that equality commutes.
* `ranOpConeLaw`: the cone law for right Kan extensions. For a transition functor, two fibre
  inclusions, an augmentation functor and two vertex functors subject to four equalities of
  composites, a cross-fibre transformation whose whiskering with the augmentation is a transport
  satisfies the cone identity between the three comparisons built from the compositor.
* `MorphismOfTopoi.inverseImage_of_directImageTransition`: the converse of
  `MorphismOfTopoi.directImageTransition_of_inverseImage`: the equation between the inverse
  images follows from the corresponding equation between the direct images.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.directImageCompatibility`: the
  compatibility of the three comparisons of direct images.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.inverseImageCompatibility`: its
  conjugate form, the compatibility of the three comparisons of inverse images.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.coneLaw`: **Stacks 0D70 (3).** A leg
  of the fork of the total augmentation, followed by the transition of the direct images of the
  components attached to a map of simplices, is again a leg.

## Implementation notes

The cone law for right Kan extensions needs no coherence hypothesis relating its four equalities
of functors. They are equalities in a type, so an equality between two of their consequences is a
proposition and holds by proof irrelevance; what has to be arranged is only that the transports
appearing in the statement run between the same functors.

The component of the situation in a simplicial degree, its topology and the total topology are
semireducible, so a term written with the underlying simplicial object of categories in place of
the component is not seen as the same term by instance synthesis, by `rw` or by `simp`, even
though the two are definitionally equal. Every functor of the situation is therefore named here
once, with its source and target spelled through the situation, and the crossing to the spelling
used by the other constructions is a single definitional type ascription in the body of that name.

The cocontinuity of each of those functors is a proposition rather than data, so it is produced
inside the proof that needs it rather than carried as a hypothesis, and the statements of the
results below mention no cocontinuity at all.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Adjunction Opposite

universe u

/-! ### The map of right Kan extensions induced by a transformation of the functors -/

section Core

variable {A : Type u} [SmallCategory A] {T : Type u} [SmallCategory T]
  {Dd : Type u} [SmallCategory Dd]

/-- The map of right Kan extensions induced by a transformation of the two functors. -/
def ranOpMap {i j : A ⥤ T} (ν : i ⟶ j) : i.op.ran (H := Type u) ⟶ j.op.ran :=
  conjugateEquiv (i.op.ranAdjunction (Type u)) (j.op.ranAdjunction (Type u))
    ((whiskeringLeft Aᵒᵖ Tᵒᵖ (Type u)).map (NatTrans.op ν))

/-- The transport of the precomposition functors along an equality of functors is conjugate to
the transport of the right Kan extensions along that equality. -/
theorem conjugateEquiv_eqToHom_precomp (F G : A ⥤ Dd) (h : F = G) :
    conjugateEquiv (F.op.ranAdjunction (Type u)) (G.op.ranAdjunction (Type u))
        (eqToHom (congrArg (fun P : A ⥤ Dd =>
          (whiskeringLeft Aᵒᵖ Ddᵒᵖ (Type u)).obj P.op) h.symm)) =
      eqToHom (congrArg (fun P : A ⥤ Dd => P.op.ran (H := Type u)) h) := by
  cases h
  simp

/-- If whiskering a transformation `ν` of two functors with a third functor `u` is the transport
along an equality `h` of the two composites, then whiskering the induced transformation of the
precomposition functors with precomposition along `u` is the transport along `h`. -/
theorem whiskerLeft_precomp_eq (i j : A ⥤ T) (u : T ⥤ Dd) (ν : i ⟶ j) (h : i ⋙ u = j ⋙ u)
    (hν : Functor.whiskerRight ν u = eqToHom h) :
    Functor.whiskerLeft ((whiskeringLeft Tᵒᵖ Ddᵒᵖ (Type u)).obj u.op)
        ((whiskeringLeft Aᵒᵖ Tᵒᵖ (Type u)).map (NatTrans.op ν)) =
      eqToHom (congrArg (fun P : A ⥤ Dd =>
        (whiskeringLeft Aᵒᵖ Ddᵒᵖ (Type u)).obj P.op) h.symm) := by
  refine NatTrans.ext (funext fun P => NatTrans.ext (funext fun X => ?_))
  have hc : u.map (ν.app X.unop) = eqToHom (Functor.congr_obj h X.unop) := by
    have hh := congrFun (congrArg NatTrans.app hν) X.unop
    simpa using hh
  change P.map ((u.map (ν.app X.unop)).op) = _
  rw [hc]
  simp [eqToHom_map, eqToHom_app]

/-- **A whiskering which is a transport is carried by the right Kan extension to the
corresponding transport.** Let `ν : i ⟶ j` be a transformation of two functors `A ⥤ T`, let
`u : T ⥤ D`, and suppose that whiskering `ν` with `u` is the transport along an equality `h` of
the two composites. Then the square formed by the map of right Kan extensions induced by `ν`, the
two compositors of Stacks 03L5 and the transport of right Kan extensions along `h` commutes. -/
theorem ranOpCompIso_ranOpMap (i j : A ⥤ T) (u : T ⥤ Dd) (ν : i ⟶ j) (h : i ⋙ u = j ⋙ u)
    (hν : Functor.whiskerRight ν u = eqToHom h) :
    (ranOpCompIso i u).hom ≫ Functor.whiskerRight (ranOpMap ν) u.op.ran =
      eqToHom (congrArg (fun P : A ⥤ Dd => P.op.ran (H := Type u)) h) ≫
        (ranOpCompIso j u).hom := by
  have hL := whiskerLeft_precomp_eq i j u ν h hν
  rw [ranOpCompIso_def, ranOpCompIso_def, rightAdjointUniq_hom_eq_conjugateEquiv,
    rightAdjointUniq_hom_eq_conjugateEquiv, ranOpMap,
    ← conjugateEquiv_whiskerLeft (i.op.ranAdjunction (Type u)) (j.op.ranAdjunction (Type u))
      (u.op.ranAdjunction (Type u)),
    ← conjugateEquiv_eqToHom_precomp (i ⋙ u) (j ⋙ u) h]
  simp only [Functor.op_comp_eq]
  rw [conjugateEquiv_comp, conjugateEquiv_comp, hL]
  congr 1

end Core

/-! ### The cone law for right Kan extensions -/

section Cone

variable {Cn : Type u} [SmallCategory Cn] {Cm : Type u} [SmallCategory Cm]
  {C0 : Type u} [SmallCategory C0] {Tt : Type u} [SmallCategory Tt]
  {Dd : Type u} [SmallCategory Dd]

/-- The compositor is compatible with a transport in its outer argument: comparing the right Kan
extension along `f ⋙ g` with the composite of the two, and then transporting the outer one along
an equality `g = g'`, is transporting along the induced equality `f ⋙ g = f ⋙ g'` and then
comparing. -/
theorem ranOpCompIso_eqToHom_right (f : Cn ⥤ Cm) {g g' : Cm ⥤ Dd} (e : g = g') :
    (ranOpCompIso f g).hom ≫ Functor.whiskerLeft f.op.ran
        (eqToHom (congrArg (fun P : Cm ⥤ Dd => P.op.ran (H := Type u)) e)) =
      eqToHom (congrArg (fun P : Cm ⥤ Dd => (f ⋙ P).op.ran (H := Type u)) e) ≫
        (ranOpCompIso f g').hom := by
  cases e
  simp

/-- The compositor is compatible with a transport in its inner argument: comparing the right Kan
extension along `g ⋙ v` with the composite of the two, and then transporting the inner one along
an equality `g = g'`, is transporting along the induced equality `g ⋙ v = g' ⋙ v` and then
comparing. -/
theorem ranOpCompIso_eqToHom_left {g g' : Cn ⥤ Cm} (v : Cm ⥤ Dd) (e : g = g') :
    (ranOpCompIso g v).hom ≫ Functor.whiskerRight
        (eqToHom (congrArg (fun P : Cn ⥤ Cm => P.op.ran (H := Type u)) e)) v.op.ran =
      eqToHom (congrArg (fun P : Cn ⥤ Cm => (P ⋙ v).op.ran (H := Type u)) e) ≫
        (ranOpCompIso g' v).hom := by
  cases e
  simp

/-- **The cone law at the level of right Kan extensions.** Let `f` be a transition functor, `inn`
and `im` two inclusions of fibres into a total category, `UU` a functor out of that total
category, `vm`, `vn` and `vn'` three functors into a degree-zero category and `aa` a functor out
of it, subject to the four equalities `em`, `en`, `hf` and `hc` of composites. Let
`ν : inn ⟶ f ⋙ im` be a cross-fibre transformation whose whiskering with `UU` is the transport
along an equality `h`. Then the map of right Kan extensions induced by `ν`, followed by the
comparison of the direct image along `im` with the one along `vm` and then by the comparison
attached to `f`, is the comparison of the direct image along `inn` with the one along `vn`. -/
theorem ranOpConeLaw (f : Cn ⥤ Cm) (im : Cm ⥤ Tt) (inn : Cn ⥤ Tt) (UU : Tt ⥤ Dd)
    (vm : Cm ⥤ C0) (vn vn' : Cn ⥤ C0) (aa : C0 ⥤ Dd)
    (ν : inn ⟶ f ⋙ im)
    (h : inn ⋙ UU = (f ⋙ im) ⋙ UU)
    (hν : Functor.whiskerRight ν UU = eqToHom h)
    (em : im ⋙ UU = vm ⋙ aa) (en : inn ⋙ UU = vn ⋙ aa)
    (hf : f ⋙ vm = vn') (hc : vn' ⋙ aa = vn ⋙ aa) :
    Functor.whiskerRight (ranOpMap ν ≫ (ranOpCompIso f im).hom) UU.op.ran ≫
        Functor.whiskerLeft f.op.ran ((ranOpCompIso im UU).inv ≫
            eqToHom (congrArg (fun P : Cm ⥤ Dd => P.op.ran (H := Type u)) em) ≫
              (ranOpCompIso vm aa).hom) ≫
          Functor.whiskerRight ((ranOpCompIso f vm).inv ≫
              eqToHom (congrArg (fun P : Cn ⥤ C0 => P.op.ran (H := Type u)) hf)) aa.op.ran ≫
            ((ranOpCompIso vn' aa).inv ≫
              eqToHom (congrArg (fun P : Cn ⥤ Dd => P.op.ran (H := Type u)) hc) ≫
                (ranOpCompIso vn aa).hom) =
      (ranOpCompIso inn UU).inv ≫
        eqToHom (congrArg (fun P : Cn ⥤ Dd => P.op.ran (H := Type u)) en) ≫
          (ranOpCompIso vn aa).hom := by
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  rw [Iso.eq_inv_comp]
  have cancelL : Functor.whiskerLeft f.op.ran (ranOpCompIso im UU).hom ≫
      Functor.whiskerLeft f.op.ran (ranOpCompIso im UU).inv = 𝟙 _ := by
    rw [← Functor.whiskerLeft_comp, Iso.hom_inv_id]
    simp
  have cancelR : Functor.whiskerRight (ranOpCompIso f vm).hom aa.op.ran ≫
      Functor.whiskerRight (ranOpCompIso f vm).inv aa.op.ran = 𝟙 _ := by
    rw [← Functor.whiskerRight_comp, Iso.hom_inv_id]
    simp
  rw [reassoc_of% (ranOpCompIso_ranOpMap inn (f ⋙ im) UU ν h hν),
    ← reassoc_of% (ranOpCompIso_assoc f im UU), reassoc_of% cancelL,
    reassoc_of% (ranOpCompIso_eqToHom_right f em),
    reassoc_of% (ranOpCompIso_assoc f vm aa), reassoc_of% cancelR,
    reassoc_of% (ranOpCompIso_eqToHom_left aa hf), Iso.hom_inv_id_assoc]
  simp only [eqToHom_trans_assoc]

end Cone

/-! ### From sheaves to presheaves -/

section Bridge

variable {Cc : Type u} [SmallCategory Cc] {Ee : Type u} [SmallCategory Ee]

/-- The transport of direct images along an equality of cocontinuous site functors acts on
underlying presheaves as the transport of right Kan extensions along that equality. -/
theorem cocontinuousPushforwardIsoOfEq_hom_app_hom (J : GrothendieckTopology Cc)
    (L : GrothendieckTopology Ee) {F G : Cc ⥤ Ee} [F.IsCocontinuous J L] [G.IsCocontinuous J L]
    (e : F = G) (X : Sheaf J (Type u)) :
    ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J L
        e).hom.app X).hom =
      (eqToHom (congrArg (fun P : Cc ⥤ Ee => P.op.ran (H := Type u)) e)).app X.obj := by
  cases e
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl]
  rfl

/-- The functor from sheaves to presheaves sends a morphism of sheaves to its underlying
morphism of presheaves. -/
theorem sheafToPresheaf_map_eq_hom (J : GrothendieckTopology Cc) {X Y : Sheaf J (Type u)}
    (f : X ⟶ Y) : (sheafToPresheaf J (Type u)).map f = f.hom := rfl

end Bridge

/-! ### The converse of the reduction of the cone law -/

namespace MorphismOfTopoi

universe v₀ u₀ v₁ u₁ v₂ u₂ v₃ u₃

variable {T : Type u₀} [Category.{v₀} T] {Dd : Type u₁} [Category.{v₁} Dd]
  {Cm : Type u₂} [Category.{v₂} Cm] {Cn : Type u₃} [Category.{v₃} Cn]

/-- **The equation between inverse images, from the equation between direct images.** This is
the converse of `MorphismOfTopoi.directImageTransition_of_inverseImage`. -/
theorem inverseImage_of_directImageTransition
    {Ai : Dd ⥤ T} {As : T ⥤ Dd} (adjA : Ai ⊣ As)
    {Rm : T ⥤ Cm} {Gm : Cm ⥤ T} (adjm : Rm ⊣ Gm)
    {Rn : T ⥤ Cn} {Gn : Cn ⥤ T} (adjn : Rn ⊣ Gn)
    {Rf : Cm ⥤ Cn} {Gf : Cn ⥤ Cm} (adjf : Rf ⊣ Gf)
    {Bmi : Dd ⥤ Cm} {Bms : Cm ⥤ Dd} (adjBm : Bmi ⊣ Bms)
    {Bni : Dd ⥤ Cn} {Bns : Cn ⥤ Dd} (adjBn : Bni ⊣ Bns)
    (pm : Gm ⋙ As ≅ Bms) (pn : Gn ⋙ As ≅ Bns) (t : Gf ⋙ Bms ≅ Bns)
    (ν : Rm ⋙ Rf ⟶ Rn)
    (hH : Functor.whiskerRight (conjugateEquiv adjn (adjm.comp adjf) ν) As ≫
      Functor.whiskerLeft Gf pm.hom ≫ t.hom = pn.hom) :
    (conjugateEquiv (adjBm.comp adjf) adjBn).symm t.hom ≫
        Functor.whiskerRight ((conjugateEquiv (adjA.comp adjm) adjBm).symm pm.hom) Rf ≫
          Functor.whiskerLeft Ai ν =
      (conjugateEquiv (adjA.comp adjn) adjBn).symm pn.hom := by
  refine (conjugateEquiv (adjA.comp adjn) adjBn).injective ?_
  rw [Equiv.apply_symm_apply, ← Category.assoc,
    ← conjugateEquiv_comp (adjA.comp adjn) (adjA.comp (adjm.comp adjf)) adjBn,
    ← conjugateEquiv_comp (adjA.comp (adjm.comp adjf)) (adjBm.comp adjf) adjBn,
    conjugateEquiv_whiskerLeft adjn (adjm.comp adjf) adjA ν]
  rw [show conjugateEquiv (adjA.comp (adjm.comp adjf)) (adjBm.comp adjf)
        (Functor.whiskerRight ((conjugateEquiv (adjA.comp adjm) adjBm).symm pm.hom) Rf) =
      Functor.whiskerLeft Gf pm.hom from by
    rw [Adjunction.comp_assoc adjA adjm adjf, conjugateEquiv_whiskerRight,
      Equiv.apply_symm_apply]]
  rw [Equiv.apply_symm_apply]
  exact hH

end MorphismOfTopoi

/-! ### The cone law for the total augmentation -/

namespace CategoryTheory

namespace CocontinuousSimplicialSite

namespace Augmentation

open CategoryTheory.SimplicialSiteSituation
open CategoryTheory.SimplicialSiteSituation.Augmentation

variable {C : CocontinuousSimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}

/-- The site functor underlying the transition morphism of topoi attached to a map of simplices,
with its source and target spelled as components of the situation. -/
def transitionSiteFunctor (C : CocontinuousSimplicialSite.{u}) {m n : SimplexCategory}
    (φ : m ⟶ n) : (situation C).component n ⥤ (situation C).component m :=
  (C.underlying.map φ.op).toFunctor

/-- The site functor attached to the constant vertex of a simplicial degree: the transition site
functor of that vertex. -/
def vertexSiteFunctor (C : CocontinuousSimplicialSite.{u}) (k : SimplexCategory) :
    (situation C).component k ⥤ (situation C).component (SimplexCategory.mk 0) :=
  transitionSiteFunctor C (SimplexCategory.const (SimplexCategory.mk 0) k 0)

/-- The cocontinuous functor of the augmentation, with its source spelled as the degree-zero
component of the situation. -/
def augSiteFunctor (a : C.Augmentation D K) :
    (situation C).component (SimplexCategory.mk 0) ⥤ D :=
  a.functor

/-- The cocontinuous functor out of the total category attached to the augmentation, with its
source spelled as the total category of the situation. -/
def totalSiteFunctor (a : C.Augmentation D K) : (situation C).totalCategory ⥤ D :=
  totalAugmentationFunctor a

/-- The cross-fibre arrows of the total category attached to a map of simplices, read as a
transformation from the inclusion of the target degree to the transition site functor followed by
the inclusion of the source degree. -/
def fibreInclusionTransition (C : CocontinuousSimplicialSite.{u}) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (situation C).inclusion n ⟶ transitionSiteFunctor C φ ⋙ (situation C).inclusion m :=
  Grothendieck.ιNatTrans φ.op

/-- The inclusion of a component followed by the functor out of the total category is the vertex
functor of that component followed by the augmentation. -/
theorem inclusion_comp_totalSiteFunctor (a : C.Augmentation D K) (k : SimplexCategory) :
    (situation C).inclusion k ⋙ totalSiteFunctor a =
      vertexSiteFunctor C k ⋙ augSiteFunctor a :=
  ι_comp_totalAugmentationFunctor a (op k)

/-- A transition site functor followed by the vertex functor of its target degree is the
transition site functor of the composite vertex. -/
theorem transitionSiteFunctor_comp_vertex (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionSiteFunctor C φ ⋙ vertexSiteFunctor C m =
      transitionSiteFunctor C (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ) :=
  (congrArg Cat.Hom.toFunctor (C.underlying.map_comp φ.op
    (SimplexCategory.const (SimplexCategory.mk 0) m 0).op)).symm

/-- The two vertices of the source degree obtained from a map of simplices and from the constant
vertex of the target degree agree after composition with the augmentation. This is the
compatibility field of the augmentation. -/
theorem transitionSiteFunctor_comp_augSiteFunctor (a : C.Augmentation D K)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionSiteFunctor C (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ) ⋙
        augSiteFunctor a =
      vertexSiteFunctor C n ⋙ augSiteFunctor a :=
  a.compatibility n (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)
    (SimplexCategory.const (SimplexCategory.mk 0) n 0)

/-- The equality of functors that the functor out of the total category transports the
cross-fibre arrows along: the inclusion of the target degree followed by that functor is the
transition site functor followed by the inclusion of the source degree and then by it. -/
theorem fibreInclusion_eq (a : C.Augmentation D K) {m n : SimplexCategory} (φ : m ⟶ n) :
    (situation C).inclusion n ⋙ totalSiteFunctor a =
      (transitionSiteFunctor C φ ⋙ (situation C).inclusion m) ⋙ totalSiteFunctor a :=
  (inclusion_comp_totalSiteFunctor a n).trans
    ((totalAugmentationFibre_eq a φ.op).trans
      (congrArg (fun P : (situation C).component m ⥤ D => transitionSiteFunctor C φ ⋙ P)
        (inclusion_comp_totalSiteFunctor a m).symm))

/-- **The functor out of the total category carries the cross-fibre arrows to a transport.**
Whiskering the cross-fibre transformation with the functor out of the total category is the
transport along `fibreInclusion_eq`. -/
theorem whiskerRight_fibreInclusionTransition (a : C.Augmentation D K)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    Functor.whiskerRight (fibreInclusionTransition C φ) (totalSiteFunctor a) =
      eqToHom (fibreInclusion_eq a φ) := by
  refine NatTrans.ext (funext fun x => Eq.trans
    (totalAugmentationFunctor_map_ιNatTrans a φ.op x) ?_)
  exact (eqToHom_app (totalAugmentationFibre_eq a φ.op) x).trans
    (eqToHom_app (fibreInclusion_eq a φ) x).symm

/-- The direct-image transition of the simplicial site acts on underlying presheaves as the
transpose, along the Kan-extension adjunction of the transition site functor, of the restriction
along the cross-fibre arrows. -/
theorem restrictTransition_app_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (situation C).totalTopology (Type u)) :
    (((situation C).restrictTransition φ).app F).hom =
      (((transitionSiteFunctor C φ).op.ranAdjunction (Type u)).homEquiv _ _)
        (Functor.whiskerRight (NatTrans.op (fibreInclusionTransition C φ)) F.obj) := rfl

/-- The direct image along a transition morphism of topoi acts on underlying presheaves as the
right Kan extension along the opposite of the transition site functor. -/
theorem transitionMorphism_pushforward_map_hom {m n : SimplexCategory} (φ : m ⟶ n)
    {X Y : Sheaf ((situation C).componentTopology n) (Type u)} (g : X ⟶ Y) :
    ((((situation C).transitionMorphism φ).pushforward).map g).hom =
      (transitionSiteFunctor C φ).op.ran.map g.hom := rfl

/-- The hom-set bijection of the adjunction between restriction to a component and the direct
image along the inclusion of that component is, on underlying presheaves, the hom-set bijection
of the Kan-extension adjunction of that inclusion. -/
theorem componentRestrictAdj_homEquiv_hom (k : SimplexCategory)
    {F : Sheaf (situation C).totalTopology (Type u)}
    {H : Sheaf ((situation C).componentTopology k) (Type u)}
    (g : ((situation C).restrict k).obj F ⟶ H) :
    ((componentRestrictAdj (C := C) k).homEquiv F H g).hom =
      ((((situation C).inclusion k).op.ranAdjunction (Type u)).homEquiv F.obj H.obj) g.hom :=
  Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom _ _ _ _ g

/-- The counit of the adjunction between restriction to a component and the direct image along
the inclusion of that component is, on underlying presheaves, the counit of the Kan-extension
adjunction of that inclusion. -/
theorem componentRestrictAdj_counit_hom (k : SimplexCategory)
    (X : Sheaf ((situation C).componentTopology k) (Type u)) :
    ((componentRestrictAdj (C := C) k).counit.app X).hom =
      (((situation C).inclusion k).op.ranAdjunction (Type u)).counit.app X.obj :=
  Functor.sheafAdjunctionCocontinuous_counit_app_hom _ _ _ _ X

/-- **The conjugate of the inverse-image transition, on underlying presheaves.** The comparison of
direct images conjugate to the inverse-image transition of the simplicial site is, on underlying
presheaves, the map of right Kan extensions induced by the cross-fibre transformation, followed by
the compositor. -/
theorem conjugateFiberTransition_app_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (X : Sheaf ((situation C).componentTopology n) (Type u)) :
    ((conjugateEquiv (componentRestrictAdj (C := C) n)
        ((componentRestrictAdj (C := C) m).comp ((situation C).transitionMorphism φ).adj)
        ((situation C).fiberTransition φ)).app X).hom =
      (ranOpMap (fibreInclusionTransition C φ) ≫
        (ranOpCompIso (transitionSiteFunctor C φ) ((situation C).inclusion m)).hom).app X.obj := by
  have hl : ((conjugateEquiv (componentRestrictAdj (C := C) n)
        ((componentRestrictAdj (C := C) m).comp ((situation C).transitionMorphism φ).adj)
        ((situation C).fiberTransition φ)).app X).hom =
      ((((situation C).inclusion m).op.ranAdjunction (Type u)).homEquiv
          (((situation C).inclusion n).op.ran.obj X.obj)
          ((transitionSiteFunctor C φ).op.ran.obj X.obj))
        ((((transitionSiteFunctor C φ).op.ranAdjunction (Type u)).homEquiv
              (((situation C).inclusion m).op ⋙ ((situation C).inclusion n).op.ran.obj X.obj)
              (((situation C).inclusion n).op ⋙ ((situation C).inclusion n).op.ran.obj X.obj))
            (Functor.whiskerRight (NatTrans.op (fibreInclusionTransition C φ))
              (((situation C).inclusion n).op.ran.obj X.obj)) ≫
          (transitionSiteFunctor C φ).op.ran.map
            ((((situation C).inclusion n).op.ranAdjunction (Type u)).counit.app X.obj)) := by
    rw [Stacks.CategoryTheory.conjugateEquiv_app_eq, Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right, SimplicialSiteSituation.fiberTransition_adj,
      componentRestrictAdj_homEquiv_hom, ObjectProperty.FullSubcategory.comp_hom,
      restrictTransition_app_hom, transitionMorphism_pushforward_map_hom,
      componentRestrictAdj_counit_hom]
    rfl
  have hr : (ranOpMap (fibreInclusionTransition C φ) ≫
        (ranOpCompIso (transitionSiteFunctor C φ)
          ((situation C).inclusion m)).hom).app X.obj =
      ((((situation C).inclusion m).op.ranAdjunction (Type u)).homEquiv
          (((situation C).inclusion n).op.ran.obj X.obj)
          ((transitionSiteFunctor C φ).op.ran.obj X.obj))
        ((((transitionSiteFunctor C φ).op.ranAdjunction (Type u)).homEquiv
              (((situation C).inclusion m).op ⋙ ((situation C).inclusion n).op.ran.obj X.obj)
              (((situation C).inclusion n).op ⋙ ((situation C).inclusion n).op.ran.obj X.obj))
            (Functor.whiskerRight (NatTrans.op (fibreInclusionTransition C φ))
              (((situation C).inclusion n).op.ran.obj X.obj)) ≫
          (transitionSiteFunctor C φ).op.ran.map
            ((((situation C).inclusion n).op.ranAdjunction (Type u)).counit.app X.obj)) := by
    rw [ranOpMap, ranOpCompIso_def, rightAdjointUniq_hom_eq_conjugateEquiv]
    simp only [Functor.op_comp_eq]
    rw [conjugateEquiv_comp, Category.id_comp,
      Stacks.CategoryTheory.conjugateEquiv_app_eq, Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right]
    rfl
  exact hl.trans hr.symm

/-- The direct image along the total augmentation acts on underlying presheaves as the right Kan
extension along the opposite of the functor out of the total category. -/
theorem totalMorphismOfTopoi_pushforward_map_hom (a : C.Augmentation D K)
    {X Y : Sheaf (situation C).totalTopology (Type u)} (g : X ⟶ Y) :
    (((totalMorphismOfTopoi a).pushforward).map g).hom =
      (totalSiteFunctor a).op.ran.map g.hom := rfl

/-- The comparison of the direct image along the inclusion of a component followed by the total
augmentation with the direct image of the augmentation of that component is, on underlying
presheaves, the inverse compositor of the inclusion and the total functor, followed by the
transport along `inclusion_comp_totalSiteFunctor` and by the compositor of the vertex functor and
the augmentation. -/
theorem componentInclusionCompPushforwardIso_hom_app_hom (a : C.Augmentation D K)
    (k : SimplexCategory)
    (hU : (totalSiteFunctor a).IsCocontinuous (situation C).totalTopology K)
    (hA : (augSiteFunctor a).IsCocontinuous
      ((situation C).componentTopology (SimplexCategory.mk 0)) K)
    (hv : (vertexSiteFunctor C k).IsCocontinuous ((situation C).componentTopology k)
      ((situation C).componentTopology (SimplexCategory.mk 0)))
    (_hi : ((situation C).inclusion k ⋙ totalSiteFunctor a).IsCocontinuous
      ((situation C).componentTopology k) K)
    (hv' : (vertexSiteFunctor C k ⋙ augSiteFunctor a).IsCocontinuous
      ((situation C).componentTopology k) K)
    (Y : Sheaf ((situation C).componentTopology k) (Type u)) :
    ((componentInclusionCompPushforwardIso a k).hom.app Y).hom =
      ((ranOpCompIso ((situation C).inclusion k) (totalSiteFunctor a)).inv ≫
        eqToHom (congrArg (fun P : (situation C).component k ⥤ D => P.op.ran (H := Type u))
            (inclusion_comp_totalSiteFunctor a k)) ≫
          (ranOpCompIso (vertexSiteFunctor C k) (augSiteFunctor a)).hom).app Y.obj := by
  rw [show componentInclusionCompPushforwardIso a k =
      (sheafPushforwardCocontinuousCompIso ((situation C).componentTopology k)
            (situation C).totalTopology K ((situation C).inclusion k)
            (totalSiteFunctor a)).symm ≪≫
        SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u}
            ((situation C).componentTopology k) K
            (inclusion_comp_totalSiteFunctor a k) ≪≫
          sheafPushforwardCocontinuousCompIso ((situation C).componentTopology k)
            ((situation C).componentTopology (SimplexCategory.mk 0)) K
            (vertexSiteFunctor C k) (augSiteFunctor a) from rfl]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, sheafPushforwardCocontinuousCompIso_inv_app_hom,
    cocontinuousPushforwardIsoOfEq_hom_app_hom,
    sheafPushforwardCocontinuousCompIso_hom_app_hom]
  rfl

/-- The comparison of the direct image of a transition followed by the direct image of the
component augmentation of its source with the direct image of the component augmentation of its
target is, on underlying presheaves, the inverse compositor of the transition and the vertex
functor followed by the transport along `transitionSiteFunctor_comp_vertex`, whiskered with the
augmentation, and then the inverse compositor of the composite vertex and the augmentation, the
transport along `transitionSiteFunctor_comp_augSiteFunctor` and the compositor of the target
vertex and the augmentation. -/
theorem transitionPushforwardIso_hom_app_hom (a : C.Augmentation D K)
    {m n : SimplexCategory} (φ : m ⟶ n)
    (hA : (augSiteFunctor a).IsCocontinuous
      ((situation C).componentTopology (SimplexCategory.mk 0)) K)
    (hvm : (vertexSiteFunctor C m).IsCocontinuous ((situation C).componentTopology m)
      ((situation C).componentTopology (SimplexCategory.mk 0)))
    (hvn : (vertexSiteFunctor C n).IsCocontinuous ((situation C).componentTopology n)
      ((situation C).componentTopology (SimplexCategory.mk 0)))
    (hf : (transitionSiteFunctor C φ).IsCocontinuous ((situation C).componentTopology n)
      ((situation C).componentTopology m))
    (_hfv : (transitionSiteFunctor C φ ⋙ vertexSiteFunctor C m).IsCocontinuous
      ((situation C).componentTopology n)
      ((situation C).componentTopology (SimplexCategory.mk 0)))
    (hw : (transitionSiteFunctor C
        (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)).IsCocontinuous
      ((situation C).componentTopology n)
      ((situation C).componentTopology (SimplexCategory.mk 0)))
    (_hwa : (transitionSiteFunctor C (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ) ⋙
        augSiteFunctor a).IsCocontinuous ((situation C).componentTopology n) K)
    (hvn' : (vertexSiteFunctor C n ⋙ augSiteFunctor a).IsCocontinuous
      ((situation C).componentTopology n) K)
    (X : Sheaf ((situation C).componentTopology n) (Type u)) :
    ((SimplicialSiteSituation.Augmentation.transitionPushforwardIso
        (situation C) D K a φ).hom.app X).hom =
      (Functor.whiskerRight ((ranOpCompIso (transitionSiteFunctor C φ)
              (vertexSiteFunctor C m)).inv ≫
            eqToHom (congrArg (fun P : (situation C).component n ⥤
                (situation C).component (SimplexCategory.mk 0) => P.op.ran (H := Type u))
              (transitionSiteFunctor_comp_vertex C φ))) (augSiteFunctor a).op.ran ≫
        ((ranOpCompIso (transitionSiteFunctor C
                (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ))
              (augSiteFunctor a)).inv ≫
          eqToHom (congrArg (fun P : (situation C).component n ⥤ D => P.op.ran (H := Type u))
              (transitionSiteFunctor_comp_augSiteFunctor a φ)) ≫
            (ranOpCompIso (vertexSiteFunctor C n) (augSiteFunctor a)).hom)).app X.obj := by
  rw [show SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation C) D K a φ =
      (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            ((sheafPushforwardCocontinuousCompIso ((situation C).componentTopology n)
                  ((situation C).componentTopology m)
                  ((situation C).componentTopology (SimplexCategory.mk 0))
                  (transitionSiteFunctor C φ) (vertexSiteFunctor C m)).symm ≪≫
              SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u}
                ((situation C).componentTopology n)
                ((situation C).componentTopology (SimplexCategory.mk 0))
                (transitionSiteFunctor_comp_vertex C φ))
            ((augSiteFunctor a).sheafPushforwardCocontinuous (Type u)
              ((situation C).componentTopology (SimplexCategory.mk 0)) K) ≪≫
        ((sheafPushforwardCocontinuousCompIso ((situation C).componentTopology n)
                ((situation C).componentTopology (SimplexCategory.mk 0)) K
                (transitionSiteFunctor C
                  (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ))
                (augSiteFunctor a)).symm ≪≫
            SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u}
              ((situation C).componentTopology n) K
              (transitionSiteFunctor_comp_augSiteFunctor a φ) ≪≫
          sheafPushforwardCocontinuousCompIso ((situation C).componentTopology n)
            ((situation C).componentTopology (SimplexCategory.mk 0)) K
            (vertexSiteFunctor C n) (augSiteFunctor a)) from rfl]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.whiskerRight_app,
    ObjectProperty.FullSubcategory.comp_hom, Category.id_comp,
    sheafPushforwardCocontinuousCompIso_inv_app_hom,
    cocontinuousPushforwardIsoOfEq_hom_app_hom,
    sheafPushforwardCocontinuousCompIso_hom_app_hom,
    Functor.sheafPushforwardCocontinuous_map_hom]
  rfl

/-- **The compatibility of the three comparisons of direct images.** The comparison of direct
images conjugate to the inverse-image transition, whiskered with the direct image of the total
augmentation, followed by the comparison of the total augmentation with the augmentation of the
source degree and then by the comparison of the component augmentations along the map of
simplices, is the comparison of the total augmentation with the augmentation of the target degree.
-/
theorem directImageCompatibility (a : C.Augmentation D K) {m n : SimplexCategory} (φ : m ⟶ n) :
    Functor.whiskerRight (conjugateEquiv (componentRestrictAdj n)
          ((componentRestrictAdj m).comp ((situation C).transitionMorphism φ).adj)
          ((situation C).fiberTransition φ))
        (totalMorphismOfTopoi a).pushforward ≫
      Functor.whiskerLeft ((situation C).transitionMorphism φ).pushforward
          (componentInclusionCompPushforwardIso a m).hom ≫
        (SimplicialSiteSituation.Augmentation.transitionPushforwardIso
          (situation C) D K a φ).hom =
      (componentInclusionCompPushforwardIso a n).hom := by
  have hU : (totalSiteFunctor a).IsCocontinuous (situation C).totalTopology K :=
    totalAugmentationFunctor_isCocontinuous a
  have hA : (augSiteFunctor a).IsCocontinuous
      ((situation C).componentTopology (SimplexCategory.mk 0)) K := a.isCocontinuous
  have hT : ∀ {k l : SimplexCategory} (ψ : k ⟶ l),
      (transitionSiteFunctor C ψ).IsCocontinuous ((situation C).componentTopology l)
        ((situation C).componentTopology k) := fun ψ => C.isCocontinuous ψ.op
  have hv : ∀ k, (vertexSiteFunctor C k).IsCocontinuous ((situation C).componentTopology k)
      ((situation C).componentTopology (SimplexCategory.mk 0)) :=
    fun k => hT (SimplexCategory.const (SimplexCategory.mk 0) k 0)
  have hv' : ∀ k, (vertexSiteFunctor C k ⋙ augSiteFunctor a).IsCocontinuous
      ((situation C).componentTopology k) K := fun k =>
    CategoryTheory.isCocontinuous_comp (vertexSiteFunctor C k) (augSiteFunctor a)
      ((situation C).componentTopology k)
      ((situation C).componentTopology (SimplexCategory.mk 0))
  have hi : ∀ k, ((situation C).inclusion k ⋙ totalSiteFunctor a).IsCocontinuous
      ((situation C).componentTopology k) K := fun k => by
    rw [inclusion_comp_totalSiteFunctor a k]
    exact hv' k
  have hfv : (transitionSiteFunctor C φ ⋙ vertexSiteFunctor C m).IsCocontinuous
      ((situation C).componentTopology n)
      ((situation C).componentTopology (SimplexCategory.mk 0)) :=
    CategoryTheory.isCocontinuous_comp (transitionSiteFunctor C φ) (vertexSiteFunctor C m)
      ((situation C).componentTopology n) ((situation C).componentTopology m)
  have hwa : (transitionSiteFunctor C
      (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ) ⋙
        augSiteFunctor a).IsCocontinuous ((situation C).componentTopology n) K :=
    CategoryTheory.isCocontinuous_comp
      (transitionSiteFunctor C (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ))
      (augSiteFunctor a) ((situation C).componentTopology n)
      ((situation C).componentTopology (SimplexCategory.mk 0))
  refine NatTrans.ext (funext fun X => (sheafToPresheaf _ _).map_injective ?_)
  have hfirst : ((Functor.whiskerRight (conjugateEquiv (componentRestrictAdj n)
            ((componentRestrictAdj m).comp ((situation C).transitionMorphism φ).adj)
            ((situation C).fiberTransition φ))
          (totalMorphismOfTopoi a).pushforward).app X).hom =
      (totalSiteFunctor a).op.ran.map ((ranOpMap (fibreInclusionTransition C φ) ≫
        (ranOpCompIso (transitionSiteFunctor C φ)
          ((situation C).inclusion m)).hom).app X.obj) :=
    congrArg (totalSiteFunctor a).op.ran.map (conjugateFiberTransition_app_hom φ X)
  have key := congrFun (congrArg NatTrans.app (ranOpConeLaw
    (transitionSiteFunctor C φ) ((situation C).inclusion m) ((situation C).inclusion n)
    (totalSiteFunctor a) (vertexSiteFunctor C m) (vertexSiteFunctor C n)
    (transitionSiteFunctor C (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ))
    (augSiteFunctor a) (fibreInclusionTransition C φ) (fibreInclusion_eq a φ)
    (whiskerRight_fibreInclusionTransition a φ)
    (inclusion_comp_totalSiteFunctor a m) (inclusion_comp_totalSiteFunctor a n)
    (transitionSiteFunctor_comp_vertex C φ) (transitionSiteFunctor_comp_augSiteFunctor a φ)))
    X.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc] at key
  simp only [sheafToPresheaf_map_eq_hom, NatTrans.comp_app, hfirst,
    Functor.whiskerLeft_app, ObjectProperty.FullSubcategory.comp_hom,
    componentInclusionCompPushforwardIso_hom_app_hom a m hU hA (hv m) (hi m) (hv' m),
    componentInclusionCompPushforwardIso_hom_app_hom a n hU hA (hv n) (hi n) (hv' n),
    transitionPushforwardIso_hom_app_hom a φ hA (hv m) (hv n) (hT φ) hfv
      (hT (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)) hwa (hv' n),
    Functor.map_comp]
  simp only [Functor.whiskerRight_app, Functor.map_comp, NatTrans.comp_app]
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · rfl

/-- **The compatibility of the three comparisons of inverse images.** The conjugate of the
comparison of the component augmentations along a map of simplices, followed by the inverse image
of the conjugate of the comparison in the source degree and by the inverse-image transition of the
simplicial site, is the conjugate of the comparison in the target degree. It is the conjugate
form of `directImageCompatibility`. -/
theorem inverseImageCompatibility (a : C.Augmentation D K) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (conjugateEquiv
            ((SimplicialSiteSituation.Augmentation.componentAugmentation
                (situation C) D K a m).adj.comp
              ((situation C).transitionMorphism φ).adj)
            (SimplicialSiteSituation.Augmentation.componentAugmentation
              (situation C) D K a n).adj).symm
          (SimplicialSiteSituation.Augmentation.transitionPushforwardIso
            (situation C) D K a φ).hom ≫
        Functor.whiskerRight
            ((conjugateEquiv ((totalMorphismOfTopoi a).adj.comp (componentRestrictAdj m))
                (SimplicialSiteSituation.Augmentation.componentAugmentation
                  (situation C) D K a m).adj).symm
              (componentInclusionCompPushforwardIso a m).hom)
            ((situation C).transitionMorphism φ).inverseImage ≫
          Functor.whiskerLeft (totalMorphismOfTopoi a).inverseImage
            ((situation C).fiberTransition φ) =
      (conjugateEquiv ((totalMorphismOfTopoi a).adj.comp (componentRestrictAdj n))
          (SimplicialSiteSituation.Augmentation.componentAugmentation
            (situation C) D K a n).adj).symm
        (componentInclusionCompPushforwardIso a n).hom :=
  MorphismOfTopoi.inverseImage_of_directImageTransition (totalMorphismOfTopoi a).adj
    (componentRestrictAdj m) (componentRestrictAdj n) ((situation C).transitionMorphism φ).adj
    (SimplicialSiteSituation.Augmentation.componentAugmentation (situation C) D K a m).adj
    (SimplicialSiteSituation.Augmentation.componentAugmentation (situation C) D K a n).adj
    (componentInclusionCompPushforwardIso a m) (componentInclusionCompPushforwardIso a n)
    (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation C) D K a φ)
    ((situation C).fiberTransition φ) (directImageCompatibility a φ)

/-- **The cone law of the total augmentation.** For every sheaf on the total site and every map
of simplices `φ : m ⟶ n`, the canonical map from the total direct image to the direct image of
the component in degree `m`, followed by the transition of the component direct images attached
to `φ`, is the canonical map to the direct image of the component in degree `n`. -/
theorem coneLaw (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n) :
    totalComponentUnitMap a F m ≫ componentDirectImageTransitionMap a F φ =
      totalComponentUnitMap a F n :=
  coneLaw_of_inverseImageCompatibility a F φ (inverseImageCompatibility a φ)

end Augmentation

end CocontinuousSimplicialSite

end CategoryTheory

end
