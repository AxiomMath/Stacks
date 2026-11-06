module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTransportedStructure
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of an inverse image of sheaves of modules

Let `g : Sh(C) ⟶ Sh(D)` be a morphism of topoi, `O` a sheaf of rings on `D`, `Φ` a point of
the site `(C, J)` and `Ψ` a point of the site `(D, K)`, and suppose the stalk functor of `Ψ`
on sheaves of sets is the inverse image along `g` followed by the stalk functor of `Φ`:

`Ψ^{-1} ≅ g^{-1} ⋙ Φ^{-1}` on `Sh(D) ⥤ Set`.

Then for every sheaf of `O`-modules `G` the stalk at `Φ` of the inverse image `g^{-1}G` is the
stalk of `G` at `Ψ`, semilinearly over the corresponding isomorphism `O_Ψ ≅ (g^{-1}O)_Φ` of
stalk rings.  This is the statement of Stacks 05V1 for sheaves of modules, at the generality of
an arbitrary morphism of topoi: the identification on underlying sets is the hypothesis, and
what is proved is that it carries the module structure.

The mechanism is that the module structure on an inverse image is a *transported* structure.
The inverse image of sheaves of modules of Stacks 03D2 is built by applying `g^{-1}` to the
scalar multiplication `O ⨯ G ⟶ G` of underlying sheaves of sets, which is legitimate because
`g^{-1}` preserves finite products; so the scalar action on the stalk at `Φ` of `g^{-1}G` is the
action transported along `g^{-1} ⋙ Φ^{-1}`, and the hypothesis identifies that functor with
`Ψ^{-1}`, under which it becomes the action transported along `Ψ^{-1}`.  The remaining step is
to replace the transported structures by the colimit-valued stalks of a sheaf of modules, which
is what `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkTransportedStructure.lean` does; the
missing half of that comparison, that it is a ring isomorphism on a sheaf of rings, is supplied
here.

## Main definitions

* `Stacks.Sheaves.StalkTransport.ringGerm`: the germ map of a sheaf of rings at a
  neighbourhood of the point, as a ring homomorphism.
* `Stacks.Sheaves.StalkInverseImage.stalkRingEquiv`: the isomorphism `O_Ψ ≅ (g^{-1}O)_Φ` of
  stalk rings.
* `Stacks.Sheaves.StalkInverseImage.stalkAddEquiv`: the isomorphism `G_Ψ ≅ (g^{-1}G)_Φ` of
  stalk modules, as an isomorphism of additive groups.

## Main results

* `Stacks.Sheaves.StalkTransport.ringStalkComparison_ringAddObj` and
  `Stacks.Sheaves.StalkTransport.ringStalkComparison_ringMulObj`: the comparison of stalks of a
  sheaf of rings is additive and multiplicative.
* `Stacks.Sheaves.ToposPullback.ringAddObj_pullbackRingSheaf` and
  `Stacks.Sheaves.ToposPullback.ringMulObj_pullbackRingSheaf`: the ring operations of an
  inverse-image sheaf of rings, read through a further finite-product-preserving functor `P`,
  are the operations of the original sheaf of rings read through `g^{-1} ⋙ P`.
* `Stacks.Sheaves.StalkInverseImage.stalkAddEquiv_smul`: **Stacks 05V1 for sheaves of
  modules.** The isomorphism of stalk modules is semilinear over the isomorphism of stalk
  rings.
* `Stacks.Sheaves.StalkInverseImage.stalkAddEquiv_naturality`: it is natural in the sheaf of
  modules.

## Implementation notes

Both comparisons of `StalkTransportedStructure.lean` are components of an isomorphism of
functors to types, hence bijective; the two equivalences below are built from those bijections
by `Equiv.ofBijective`, and every algebraic property is proved by transporting a germ
computation through them.  No inverse is ever computed: a statement about the inverse direction
is obtained by naming a preimage with `Function.Surjective` and rewriting forwards.

The three algebraic steps are kept separate, one for each of the three functors involved.  For
the transported action they are: the germ comparison at `Ψ`
(`moduleStalkComparison_moduleSMulObj`), naturality of the transported action in the
finite-product-preserving functor (`Sheaf.moduleSMulObj_naturality`, applied to the hypothesised
isomorphism), and the identification of the transported action on an inverse image
(`Stacks.Sheaves.ToposPullback.moduleSMulObj_pullbackModuleObj`).  The ring-level analogue of
the third is proved here, the existing file having only the module-level one.

The hypothesis on `Φ`, `Ψ` and `g` is taken as a datum rather than derived.  For a morphism of
topoi coming from a morphism of sites it is part (2) of Stacks 00YA, which produces the point
`Ψ` of the target site *together with* this identification; taking the identification as the
input keeps the statement free of any smallness condition on the two sites.

## References

* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

/- Since Mathlib v4.35.0, instance search for the product of two underlying sheaves of sets of
sheaves of rings first tries this instance (products of images under the forgetful functor),
which searches for limits of presheaves of rings and times out; the products are found directly
without it. -/
attribute [-instance]
  CategoryTheory.Limits.instHasBinaryProductObjOfPreservesLimitDiscreteWalkingPairPair

/-! ### The comparison of stalk rings is a ring isomorphism -/

namespace Stacks.Sheaves.StalkTransport

universe w v u

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (Φ : J.Point.{w}) (R : Sheaf J RingCat.{w})

/-- The germ map of a sheaf of rings at a neighbourhood `(U, z)` of the point, as a ring
homomorphism to the stalk ring. -/
def ringGerm (U : C) (z : Φ.fiber.obj U) :
    R.obj.obj (op U) →+* (Φ.presheafFiber (A := RingCat.{w})).obj R.obj :=
  (Φ.toPresheafFiber U z R.obj).hom

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The comparison of stalks of a sheaf of rings carries a germ to the corresponding germ,
stated with the bundled ring homomorphism `Stacks.Sheaves.StalkTransport.ringGerm`. -/
lemma ringStalkComparison_ringGerm (U : C) (z : Φ.fiber.obj U)
    (s : (Sheaf.ringSheaf R).obj.obj (op U)) :
    ringStalkComparison Φ R (Φ.toPresheafFiber U z (Sheaf.ringSheaf R).obj s) =
      ringGerm Φ R U z s :=
  ringStalkComparison_germ Φ R U z s

omit [LocallySmall.{w} C] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The germ of a section of the product of the underlying sheaves of sets of a sheaf of rings
with itself has the germ of its first component as its image under the first projection. -/
lemma map_fst_toPresheafFiber_ring (U : C) (z : Φ.fiber.obj U)
    (p : (Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R).obj.obj (op U)) :
    (Φ.sheafFiber (A := Type w)).map (prod.fst : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ _)
        (Φ.toPresheafFiber U z (Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R).obj p) =
      Φ.toPresheafFiber U z (Sheaf.ringSheaf R).obj
        ((prod.fst : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ _).hom.app (op U) p) :=
  Φ.toPresheafFiber_naturality_apply
    (prod.fst : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ _).hom U z p

omit [LocallySmall.{w} C] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The germ of a section of the product of the underlying sheaves of sets of a sheaf of rings
with itself has the germ of its second component as its image under the second projection. -/
lemma map_snd_toPresheafFiber_ring (U : C) (z : Φ.fiber.obj U)
    (p : (Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R).obj.obj (op U)) :
    (Φ.sheafFiber (A := Type w)).map (prod.snd : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ _)
        (Φ.toPresheafFiber U z (Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R).obj p) =
      Φ.toPresheafFiber U z (Sheaf.ringSheaf R).obj
        ((prod.snd : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ _).hom.app (op U) p) :=
  Φ.toPresheafFiber_naturality_apply
    (prod.snd : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ _).hom U z p

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in /-- Two ring germs come from one section. -/
  private lemma exists_germ_pair_ring
    (x y : (Φ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf R)) :
    ∃ (U : C) (z : Φ.fiber.obj U) (p : (Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R).obj.obj (op U)),
      x = Φ.toPresheafFiber U z (Sheaf.ringSheaf R).obj
        ((prod.fst : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ _).hom.app (op U) p) ∧
      y = Φ.toPresheafFiber U z (Sheaf.ringSheaf R).obj
        ((prod.snd : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ _).hom.app (op U) p) ∧
      ∀ f : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ Sheaf.ringSheaf R,
        (Φ.sheafFiber (A := Type w)).map f (Functor.prodObjMk x y) =
          Φ.toPresheafFiber U z (Sheaf.ringSheaf R).obj (f.hom.app (op U) p) := by
  obtain ⟨U, z, p, hp⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := (Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R).obj)
    (Functor.prodObjMk (P := Φ.sheafFiber (A := Type w)) x y)
  refine ⟨U, z, p, ?_, ?_, fun f ↦ ?_⟩
  · rw [← map_fst_toPresheafFiber_ring Φ R U z p, hp, Functor.map_fst_prodObjMk]
  · rw [← map_snd_toPresheafFiber_ring Φ R U z p, hp, Functor.map_snd_prodObjMk]
  · rw [← hp]
    exact Φ.toPresheafFiber_naturality_apply f.hom U z p

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The comparison of stalk rings is additive.** -/
lemma ringStalkComparison_ringAddObj
    (x y : (Φ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf R)) :
    ringStalkComparison Φ R (Sheaf.ringAddObj R (Φ.sheafFiber (A := Type w)) x y) =
      ringStalkComparison Φ R x + ringStalkComparison Φ R y := by
  obtain ⟨U, z, p, hx, hy, hf⟩ := exists_germ_pair_ring Φ R x y
  rw [Sheaf.ringAddObj, hf, hx, hy, ringStalkComparison_ringGerm, ringStalkComparison_ringGerm,
    ringStalkComparison_ringGerm]
  exact map_add (ringGerm Φ R U z) _ _

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The comparison of stalk rings is multiplicative.** -/
lemma ringStalkComparison_ringMulObj
    (x y : (Φ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf R)) :
    ringStalkComparison Φ R (Sheaf.ringMulObj R (Φ.sheafFiber (A := Type w)) x y) =
      ringStalkComparison Φ R x * ringStalkComparison Φ R y := by
  obtain ⟨U, z, p, hx, hy, hf⟩ := exists_germ_pair_ring Φ R x y
  rw [Sheaf.ringMulObj, hf, hx, hy, ringStalkComparison_ringGerm, ringStalkComparison_ringGerm,
    ringStalkComparison_ringGerm]
  exact map_mul (ringGerm Φ R U z) _ _

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The comparison of stalks of a sheaf of rings is bijective, being a component of an
isomorphism of functors to types. -/
lemma bijective_ringStalkComparison : Function.Bijective (ringStalkComparison Φ R) := by
  have h : IsIso ((Φ.presheafFiberCompIso (forget RingCat.{w})).hom.app R.obj) := inferInstance
  exact (isIso_iff_bijective _).1 h

variable (G : SheafOfModules.{w} R)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The comparison of stalks of a sheaf of modules is bijective, being a component of an
isomorphism of functors to types. -/
lemma bijective_moduleStalkComparison :
    Function.Bijective (moduleStalkComparison Φ R G) := by
  have h : IsIso ((Φ.presheafFiberCompIso (forget AddCommGrpCat.{w})).hom.app G.val.presheaf) :=
    inferInstance
  exact (isIso_iff_bijective _).1 h

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The comparison of stalks of a sheaf of modules is natural in the sheaf of modules. -/
lemma moduleStalkComparison_naturality {G G' : SheafOfModules.{w} R} (α : G ⟶ G')
    (m : (Φ.sheafFiber (A := Type w)).obj (Sheaf.moduleSheaf R G)) :
    moduleStalkComparison Φ R G'
        ((Φ.sheafFiber (A := Type w)).map ((Sheaf.moduleSheafFunctor R).map α) m) =
      (Stacks.sheafModuleFiber Φ R).map α (moduleStalkComparison Φ R G m) :=
  ConcreteCategory.congr_hom
    ((Φ.presheafFiberCompIso (forget AddCommGrpCat.{w})).hom.naturality
      ((PresheafOfModules.toPresheaf R.obj).map ((SheafOfModules.forget R).map α))) m

end Stacks.Sheaves.StalkTransport

/-! ### The ring operations of an inverse-image sheaf of rings -/

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory.Sheaf

universe t ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})

/-- A binary operation `f'` on the inverse-image sheaf of rings, whose image under `Φ` of the
operation `f` on `O` is the product comparison followed by `f'`, is read through `P` as `f`
read through `Φ ⋙ P`. -/
private lemma map_prodObjMk_pullbackRingSheaf (P : Sheaf J (Type ww) ⥤ Type t)
    [PreservesFiniteProducts P] (f : Sheaf.ringSheaf O ⨯ Sheaf.ringSheaf O ⟶ Sheaf.ringSheaf O)
    (f' : Sheaf.ringSheaf (pullbackRingSheaf J Φ O) ⨯ Sheaf.ringSheaf (pullbackRingSheaf J Φ O) ⟶
      Sheaf.ringSheaf (pullbackRingSheaf J Φ O))
    (h : Φ.map f = prodComparison Φ _ _ ≫ f') (x y : P.obj (Φ.obj (Sheaf.ringSheaf O))) :
    P.map f' (Functor.prodObjMk (P := P) x y) =
      (Φ ⋙ P).map f (Functor.prodObjMk (P := Φ ⋙ P) x y) := by
  have : PreservesFiniteProducts (Φ ⋙ P) := inferInstance
  refine Eq.symm (Eq.trans (congrArg
    (fun n ↦ P.map n (Functor.prodObjMk (P := Φ ⋙ P) x y)) h) ?_)
  refine Eq.trans (P.map_comp_apply _ _ _) ?_
  congr 1
  rw [Functor.map_prodComparison_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]
  rfl

/-- **Stacks 03D2**, ring addition read through a further functor.  The addition of the
inverse-image sheaf of rings along `Φ`, transported to the image of a finite-product-preserving
functor `P` to types, is the addition of the original sheaf of rings transported along
`Φ ⋙ P`.

This is the ring-level counterpart of
`Stacks.Sheaves.ToposPullback.moduleAddObj_pullbackModuleObj`. -/
lemma ringAddObj_pullbackRingSheaf (P : Sheaf J (Type ww) ⥤ Type t)
    [PreservesFiniteProducts P] (x y : P.obj (Φ.obj (Sheaf.ringSheaf O))) :
    Sheaf.ringAddObj (pullbackRingSheaf J Φ O) P x y = Sheaf.ringAddObj O (Φ ⋙ P) x y :=
  map_prodObjMk_pullbackRingSheaf J Φ O P _ _ (ringAdd_map_aux' J Φ O) x y

/-- **Stacks 03D2**, ring multiplication read through a further functor.  The multiplication of
the inverse-image sheaf of rings along `Φ`, transported to the image of a
finite-product-preserving functor `P` to types, is the multiplication of the original sheaf of
rings transported along `Φ ⋙ P`. -/
lemma ringMulObj_pullbackRingSheaf (P : Sheaf J (Type ww) ⥤ Type t)
    [PreservesFiniteProducts P] (x y : P.obj (Φ.obj (Sheaf.ringSheaf O))) :
    Sheaf.ringMulObj (pullbackRingSheaf J Φ O) P x y = Sheaf.ringMulObj O (Φ ⋙ P) x y :=
  map_prodObjMk_pullbackRingSheaf J Φ O P _ _ (ringMul_map_aux' J Φ O) x y

end Stacks.Sheaves.ToposPullback

/-! ### Stacks 05V1 for sheaves of modules -/

namespace Stacks.Sheaves.StalkInverseImage

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.StalkTransport

universe w v u v' u'

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [LocallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})]
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  [PreservesFiniteLimits g.inverseImage]
  (O : Sheaf K RingCat.{w}) (Φ : J.Point.{w}) (Ψ : K.Point.{w})
  (e : Ψ.sheafFiber (A := Type w) ≅ g.inverseImage ⋙ Φ.sheafFiber (A := Type w))

/-! #### The comparison at `Φ`, read on the inverse image of a sheaf of sets -/

omit [LocallySmall.{w} D] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The comparison of stalk rings at `Φ` is additive, read on the inverse image along `g` of
the underlying sheaf of sets of `O`.

The two spellings of the inverse-image sheaf of rings — the transported structure on
`g⁻¹O` and the sheaf of rings `inverseImageRingSheaf g O` — are definitionally equal, and this
is where they are identified, once; every statement below is in the first spelling. -/
private lemma ringCmp_add
    (x y : (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf O)) :
    ringStalkComparison Φ (inverseImageRingSheaf g O)
        (Sheaf.ringAddObj O (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)) x y) =
      ringStalkComparison Φ (inverseImageRingSheaf g O) x +
        ringStalkComparison Φ (inverseImageRingSheaf g O) y :=
  (congrArg (ringStalkComparison Φ (inverseImageRingSheaf g O))
      (ringAddObj_pullbackRingSheaf J g.inverseImage O
        (Φ.sheafFiber (A := Type w)) x y).symm).trans
    (ringStalkComparison_ringAddObj Φ (inverseImageRingSheaf g O) x y)

omit [LocallySmall.{w} D] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The comparison of stalk rings at `Φ` is multiplicative, read on the inverse image along `g`
of the underlying sheaf of sets of `O`. -/
private lemma ringCmp_mul
    (x y : (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf O)) :
    ringStalkComparison Φ (inverseImageRingSheaf g O)
        (Sheaf.ringMulObj O (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)) x y) =
      ringStalkComparison Φ (inverseImageRingSheaf g O) x *
        ringStalkComparison Φ (inverseImageRingSheaf g O) y :=
  (congrArg (ringStalkComparison Φ (inverseImageRingSheaf g O))
      (ringMulObj_pullbackRingSheaf J g.inverseImage O
        (Φ.sheafFiber (A := Type w)) x y).symm).trans
    (ringStalkComparison_ringMulObj Φ (inverseImageRingSheaf g O) x y)

/-! #### The comparison of stalk rings -/

/-- **The comparison `O_Ψ ⟶ (g⁻¹O)_Φ` of stalk rings.**  On underlying sets it is the
hypothesised identification of stalk functors on sheaves of sets, read between the two stalks
of a sheaf of rings. -/
def stalkRingMap : (Ψ.presheafFiber (A := RingCat.{w})).obj O.obj →
    (Φ.presheafFiber (A := RingCat.{w})).obj (inverseImageRingSheaf g O).obj :=
  fun r ↦ ringStalkComparison Φ (inverseImageRingSheaf g O)
    (e.hom.app (Sheaf.ringSheaf O)
      ((Equiv.ofBijective _ (bijective_ringStalkComparison Ψ O)).symm r))

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})]
  [PreservesFiniteLimits g.inverseImage] in
/-- The comparison of stalk rings, evaluated on a germ presented through the comparison of the
two stalks at `Ψ`. -/
lemma stalkRingMap_ringStalkComparison
    (x : (Ψ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf O)) :
    stalkRingMap g O Φ Ψ e (ringStalkComparison Ψ O x) =
      ringStalkComparison Φ (inverseImageRingSheaf g O) (e.hom.app (Sheaf.ringSheaf O) x) :=
  congrArg
    (fun u ↦ ringStalkComparison Φ (inverseImageRingSheaf g O)
      (e.hom.app (Sheaf.ringSheaf O) u))
    ((Equiv.ofBijective _ (bijective_ringStalkComparison Ψ O)).symm_apply_apply x)

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})]
  [PreservesFiniteLimits g.inverseImage] in
/-- The comparison of stalk rings is bijective. -/
lemma bijective_stalkRingMap : Function.Bijective (stalkRingMap g O Φ Ψ e) :=
  (bijective_ringStalkComparison Φ (inverseImageRingSheaf g O)).comp
    (((isIso_iff_bijective (e.hom.app (Sheaf.ringSheaf O))).1 inferInstance).comp
      (Equiv.ofBijective _ (bijective_ringStalkComparison Ψ O)).symm.bijective)

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The comparison of stalk rings is additive. -/
lemma stalkRingMap_add (a b : (Ψ.presheafFiber (A := RingCat.{w})).obj O.obj) :
    stalkRingMap g O Φ Ψ e (a + b) =
      stalkRingMap g O Φ Ψ e a + stalkRingMap g O Φ Ψ e b := by
  obtain ⟨x, hx⟩ := (bijective_ringStalkComparison Ψ O).2 a
  obtain ⟨y, hy⟩ := (bijective_ringStalkComparison Ψ O).2 b
  subst hx
  subst hy
  rw [← ringStalkComparison_ringAddObj Ψ O x y, stalkRingMap_ringStalkComparison,
    stalkRingMap_ringStalkComparison, stalkRingMap_ringStalkComparison,
    Sheaf.ringAddObj_naturality O e.hom x y, ringCmp_add]

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The comparison of stalk rings is multiplicative. -/
lemma stalkRingMap_mul (a b : (Ψ.presheafFiber (A := RingCat.{w})).obj O.obj) :
    stalkRingMap g O Φ Ψ e (a * b) =
      stalkRingMap g O Φ Ψ e a * stalkRingMap g O Φ Ψ e b := by
  obtain ⟨x, hx⟩ := (bijective_ringStalkComparison Ψ O).2 a
  obtain ⟨y, hy⟩ := (bijective_ringStalkComparison Ψ O).2 b
  subst hx
  subst hy
  rw [← ringStalkComparison_ringMulObj Ψ O x y, stalkRingMap_ringStalkComparison,
    stalkRingMap_ringStalkComparison, stalkRingMap_ringStalkComparison,
    Sheaf.ringMulObj_naturality O e.hom x y, ringCmp_mul]

/-- **The isomorphism `O_Ψ ≅ (g⁻¹O)_Φ` of stalk rings.** -/
def stalkRingEquiv :
    (Ψ.presheafFiber (A := RingCat.{w})).obj O.obj ≃+*
      (Φ.presheafFiber (A := RingCat.{w})).obj (inverseImageRingSheaf g O).obj :=
  { Equiv.ofBijective _ (bijective_stalkRingMap g O Φ Ψ e) with
    map_mul' := stalkRingMap_mul g O Φ Ψ e
    map_add' := stalkRingMap_add g O Φ Ψ e }

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The isomorphism `stalkRingEquiv` of stalk rings is given by `stalkRingMap`. -/
@[simp]
lemma stalkRingEquiv_apply (r : (Ψ.presheafFiber (A := RingCat.{w})).obj O.obj) :
    stalkRingEquiv g O Φ Ψ e r = stalkRingMap g O Φ Ψ e r := rfl

/-! #### The comparison of stalk modules -/

section Module

variable (G : SheafOfModules.{w} O)

omit [LocallySmall.{w} D] [J.HasSheafCompose (forget RingCat.{w})] in
/-- The comparison of stalk modules at `Φ` is additive, read on the inverse image along `g` of
the underlying sheaf of sets of `G`. -/
private lemma moduleCmp_add
    (m n : (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)).obj (Sheaf.moduleSheaf O G)) :
    moduleStalkComparison Φ (inverseImageRingSheaf g O) ((inverseImageModules g O).obj G)
        (Sheaf.moduleAddObj O G (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)) m n) =
      moduleStalkComparison Φ (inverseImageRingSheaf g O) ((inverseImageModules g O).obj G) m +
        moduleStalkComparison Φ (inverseImageRingSheaf g O)
          ((inverseImageModules g O).obj G) n :=
  (congrArg (moduleStalkComparison Φ (inverseImageRingSheaf g O)
        ((inverseImageModules g O).obj G))
      (moduleAddObj_pullbackModuleObj J g.inverseImage O G
        (Φ.sheafFiber (A := Type w)) m n).symm).trans
    (moduleStalkComparison_moduleAddObj Φ (inverseImageRingSheaf g O)
      ((inverseImageModules g O).obj G) m n)

omit [LocallySmall.{w} D] in
/-- The comparison of stalk modules at `Φ` is semilinear over the comparison of stalk rings at
`Φ`, read on the inverse images along `g` of the underlying sheaves of sets. -/
private lemma moduleCmp_smul
    (r : (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf O))
    (m : (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)).obj (Sheaf.moduleSheaf O G)) :
    moduleStalkComparison Φ (inverseImageRingSheaf g O) ((inverseImageModules g O).obj G)
        (Sheaf.moduleSMulObj O G (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)) r m) =
      ringStalkComparison Φ (inverseImageRingSheaf g O) r •
        moduleStalkComparison Φ (inverseImageRingSheaf g O)
          ((inverseImageModules g O).obj G) m :=
  (congrArg (moduleStalkComparison Φ (inverseImageRingSheaf g O)
        ((inverseImageModules g O).obj G))
      (moduleSMulObj_pullbackModuleObj J g.inverseImage O G
        (Φ.sheafFiber (A := Type w)) r m).symm).trans
    (moduleStalkComparison_moduleSMulObj Φ (inverseImageRingSheaf g O)
      ((inverseImageModules g O).obj G) r m)

/-- **The comparison `G_Ψ ⟶ (g⁻¹G)_Φ` of stalk modules.** -/
def stalkModuleMap : (Stacks.sheafModuleFiber Ψ O).obj G →
    (Stacks.sheafModuleFiber Φ (inverseImageRingSheaf g O)).obj
      ((inverseImageModules g O).obj G) :=
  fun m ↦ moduleStalkComparison Φ (inverseImageRingSheaf g O) ((inverseImageModules g O).obj G)
    (e.hom.app (Sheaf.moduleSheaf O G)
      ((Equiv.ofBijective _ (bijective_moduleStalkComparison Ψ O G)).symm m))

omit [J.HasSheafCompose (forget RingCat.{w})] [PreservesFiniteLimits g.inverseImage] in
/-- The comparison of stalk modules, evaluated on a germ presented through the comparison of
the two stalks at `Ψ`. -/
lemma stalkModuleMap_moduleStalkComparison
    (x : (Ψ.sheafFiber (A := Type w)).obj (Sheaf.moduleSheaf O G)) :
    stalkModuleMap g O Φ Ψ e G (moduleStalkComparison Ψ O G x) =
      moduleStalkComparison Φ (inverseImageRingSheaf g O) ((inverseImageModules g O).obj G)
        (e.hom.app (Sheaf.moduleSheaf O G) x) :=
  congrArg
    (fun u ↦ moduleStalkComparison Φ (inverseImageRingSheaf g O)
      ((inverseImageModules g O).obj G) (e.hom.app (Sheaf.moduleSheaf O G) u))
    ((Equiv.ofBijective _ (bijective_moduleStalkComparison Ψ O G)).symm_apply_apply x)

omit [J.HasSheafCompose (forget RingCat.{w})] [PreservesFiniteLimits g.inverseImage] in
/-- The comparison of stalk modules is bijective. -/
lemma bijective_stalkModuleMap : Function.Bijective (stalkModuleMap g O Φ Ψ e G) :=
  (bijective_moduleStalkComparison Φ (inverseImageRingSheaf g O)
      ((inverseImageModules g O).obj G)).comp
    (((isIso_iff_bijective (e.hom.app (Sheaf.moduleSheaf O G))).1 inferInstance).comp
      (Equiv.ofBijective _ (bijective_moduleStalkComparison Ψ O G)).symm.bijective)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The comparison of stalk modules is additive. -/
lemma stalkModuleMap_add (a b : (Stacks.sheafModuleFiber Ψ O).obj G) :
    stalkModuleMap g O Φ Ψ e G (a + b) =
      stalkModuleMap g O Φ Ψ e G a + stalkModuleMap g O Φ Ψ e G b := by
  obtain ⟨x, hx⟩ := (bijective_moduleStalkComparison Ψ O G).2 a
  obtain ⟨y, hy⟩ := (bijective_moduleStalkComparison Ψ O G).2 b
  subst hx
  subst hy
  rw [← moduleStalkComparison_moduleAddObj Ψ O G x y, stalkModuleMap_moduleStalkComparison,
    stalkModuleMap_moduleStalkComparison, stalkModuleMap_moduleStalkComparison,
    Sheaf.moduleAddObj_naturality O G e.hom x y, moduleCmp_add]

/-- The stalk at `Φ` of the inverse image along `g` of a sheaf of `O`-modules is the stalk of
that sheaf at `Ψ`, as an isomorphism of additive groups. It is semilinear over
`Stacks.Sheaves.StalkInverseImage.stalkRingEquiv`; see
`Stacks.Sheaves.StalkInverseImage.stalkAddEquiv_smul`. -/
@[stacks 05V1 "for sheaves of modules, at a point of a site, for a morphism of topoi whose
stalk functor at the target point is the inverse image followed by the stalk functor at the
source point"]
def stalkAddEquiv :
    (Stacks.sheafModuleFiber Ψ O).obj G ≃+
      (Stacks.sheafModuleFiber Φ (inverseImageRingSheaf g O)).obj
        ((inverseImageModules g O).obj G) :=
  { Equiv.ofBijective _ (bijective_stalkModuleMap g O Φ Ψ e G) with
    map_add' := stalkModuleMap_add g O Φ Ψ e G }

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The isomorphism `stalkAddEquiv` of stalk modules is given by `stalkModuleMap`. -/
@[simp]
lemma stalkAddEquiv_apply (m : (Stacks.sheafModuleFiber Ψ O).obj G) :
    stalkAddEquiv g O Φ Ψ e G m = stalkModuleMap g O Φ Ψ e G m := rfl

/-- The comparison of stalk modules is semilinear over the comparison of stalk rings. -/
theorem stalkModuleMap_smul (r : (Ψ.presheafFiber (A := RingCat.{w})).obj O.obj)
    (m : (Stacks.sheafModuleFiber Ψ O).obj G) :
    stalkModuleMap g O Φ Ψ e G (r • m) =
      stalkRingMap g O Φ Ψ e r • stalkModuleMap g O Φ Ψ e G m := by
  obtain ⟨ρ, hρ⟩ := (bijective_ringStalkComparison Ψ O).2 r
  obtain ⟨x, hx⟩ := (bijective_moduleStalkComparison Ψ O G).2 m
  subst hρ
  subst hx
  rw [← moduleStalkComparison_moduleSMulObj Ψ O G ρ x, stalkModuleMap_moduleStalkComparison,
    stalkModuleMap_moduleStalkComparison, stalkRingMap_ringStalkComparison,
    Sheaf.moduleSMulObj_naturality O G e.hom ρ x, moduleCmp_smul]

/-- The isomorphism of stalk modules is semilinear over the isomorphism of stalk rings: the
stalk at `Φ` of the inverse image of `G` is the stalk of `G` at `Ψ`, with the scalars carried
along `O_Ψ ≅ (g⁻¹O)_Φ`. -/
@[stacks 05V1 "semilinearity of the comparison, for sheaves of modules"]
theorem stalkAddEquiv_smul (r : (Ψ.presheafFiber (A := RingCat.{w})).obj O.obj)
    (m : (Stacks.sheafModuleFiber Ψ O).obj G) :
    stalkAddEquiv g O Φ Ψ e G (r • m) =
      stalkRingEquiv g O Φ Ψ e r • stalkAddEquiv g O Φ Ψ e G m :=
  stalkModuleMap_smul g O Φ Ψ e G r m

end Module

/-! #### Naturality in the sheaf of modules -/

section Naturality

variable {G G' : SheafOfModules.{w} O} (α : G ⟶ G')

omit [LocallySmall.{w} D] [J.HasSheafCompose (forget RingCat.{w})]
  [PreservesFiniteLimits g.inverseImage] in
/-- The comparison of stalk modules at `Φ` is natural in the sheaf of modules, read on the
inverse images along `g` of the underlying sheaves of sets. -/
private lemma moduleCmp_naturality
    (m : (g.inverseImage ⋙ Φ.sheafFiber (A := Type w)).obj (Sheaf.moduleSheaf O G)) :
    moduleStalkComparison Φ (inverseImageRingSheaf g O) ((inverseImageModules g O).obj G')
        ((g.inverseImage ⋙ Φ.sheafFiber (A := Type w)).map
          ((Sheaf.moduleSheafFunctor O).map α) m) =
      (Stacks.sheafModuleFiber Φ (inverseImageRingSheaf g O)).map
        ((inverseImageModules g O).map α)
        (moduleStalkComparison Φ (inverseImageRingSheaf g O)
          ((inverseImageModules g O).obj G) m) :=
  moduleStalkComparison_naturality Φ (inverseImageRingSheaf g O)
    ((inverseImageModules g O).map α) m

omit [J.HasSheafCompose (forget RingCat.{w})] [PreservesFiniteLimits g.inverseImage] in
/-- The comparison of stalk modules is natural in the sheaf of modules. -/
theorem stalkModuleMap_naturality (m : (Stacks.sheafModuleFiber Ψ O).obj G) :
    stalkModuleMap g O Φ Ψ e G' ((Stacks.sheafModuleFiber Ψ O).map α m) =
      (Stacks.sheafModuleFiber Φ (inverseImageRingSheaf g O)).map
        ((inverseImageModules g O).map α) (stalkModuleMap g O Φ Ψ e G m) := by
  obtain ⟨x, hx⟩ := (bijective_moduleStalkComparison Ψ O G).2 m
  subst hx
  rw [← moduleStalkComparison_naturality Ψ O α x, stalkModuleMap_moduleStalkComparison,
    stalkModuleMap_moduleStalkComparison, ← moduleCmp_naturality g O Φ α]
  refine congrArg
    (moduleStalkComparison Φ (inverseImageRingSheaf g O) ((inverseImageModules g O).obj G')) ?_
  rw [← types_comp_apply ((Ψ.sheafFiber (A := Type w)).map
      ((Sheaf.moduleSheafFunctor O).map α)) (e.hom.app (Sheaf.moduleSheaf O G')),
    e.hom.naturality, types_comp_apply]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The isomorphism of stalk modules is natural in the sheaf of modules. -/
theorem stalkAddEquiv_naturality (m : (Stacks.sheafModuleFiber Ψ O).obj G) :
    stalkAddEquiv g O Φ Ψ e G' ((Stacks.sheafModuleFiber Ψ O).map α m) =
      (Stacks.sheafModuleFiber Φ (inverseImageRingSheaf g O)).map
        ((inverseImageModules g O).map α) (stalkAddEquiv g O Φ Ψ e G m) :=
  stalkModuleMap_naturality g O Φ Ψ e α m

end Naturality

/-! #### The comparison as a natural isomorphism of stalk functors -/

section NatIso

/-- **Module-level Stacks 05V1 as a linear equivalence.**  The stalk of `G` at `Ψ` is the
stalk at `Φ` of the inverse image of `G`, with its scalars restricted along the isomorphism
`O_Ψ ≅ (g⁻¹O)_Φ` of stalk rings. -/
def stalkLinearEquiv (G : SheafOfModules.{w} O) :
    (Stacks.sheafModuleFiber Ψ O).obj G ≃ₗ[(Ψ.presheafFiber (A := RingCat.{w})).obj O.obj]
      (ModuleCat.restrictScalars (stalkRingEquiv g O Φ Ψ e).toRingHom).obj
        ((Stacks.sheafModuleFiber Φ (inverseImageRingSheaf g O)).obj
          ((inverseImageModules g O).obj G)) :=
  { stalkAddEquiv g O Φ Ψ e G with
    map_smul' := stalkAddEquiv_smul g O Φ Ψ e G }

/-- The stalk functor at `Ψ` is the inverse image of sheaves of modules followed by the stalk
functor at `Φ` and restriction of scalars along the isomorphism of stalk rings. -/
@[stacks 05V1 "for sheaves of modules, as a natural isomorphism of stalk functors"]
def stalkNatIso :
    Stacks.sheafModuleFiber Ψ O ≅
      inverseImageModules g O ⋙ Stacks.sheafModuleFiber Φ (inverseImageRingSheaf g O) ⋙
        ModuleCat.restrictScalars (stalkRingEquiv g O Φ Ψ e).toRingHom :=
  NatIso.ofComponents (fun G ↦ (stalkLinearEquiv g O Φ Ψ e G).toModuleIso)
    (fun α ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦
      stalkAddEquiv_naturality g O Φ Ψ e α m))

end NatIso

end Stacks.Sheaves.StalkInverseImage

end

end
