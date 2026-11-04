module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.DescentUniqueness
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeDescent
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeGluing
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeLocallyBijective

/-!
# Effective descent for the third stage

For a fibred category whose morphism presheaves are sheaves and whose locally equal morphisms are
equal, we construct the gluing isomorphisms of the amalgamated descent pair of the third stage of
the stackification, and prove that descent data in the third stage are effective.

## Main definitions

* `CategoryTheory.Functor.SieveDescentDatum.transportObj`: a descent datum transported along a
  family of isomorphisms of its objects.
* `CategoryTheory.Functor.SieveDescentDatum.descendAlong`: for a 1-morphism of fibred categories
  whose functors on fibres are fully faithful, the descent datum in the source obtained from a
  descent datum in the target whose objects are isomorphic to images of objects of the source.
* `CategoryTheory.Functor.DescentPair.datumHom`: the canonical morphism from the descent pair of an
  object of the datum of a descent pair to the pair itself.
* `CategoryTheory.Functor.SieveDescentDatum.gluePair`: the descent pair that a descent datum of
  descent pairs amalgamates to.

## Main results

* `CategoryTheory.Functor.exists_fiberIso_of_toDescentPair_iso`: the functors induced on fibres by
  the 1-morphism into the third stage are full on isomorphisms.
* `CategoryTheory.Functor.SieveDescentDatum.isEffective_of_restrict`: effectiveness of a descent
  datum is local on the base.
* `CategoryTheory.Functor.DescentPair.ofFiberMor_contract_comp_datumHom`: the canonical morphisms
  from the pairs of the objects of a descent datum are compatible with its contractions.
* `CategoryTheory.Functor.hasEffectiveDescent_descentPairProj`: every descent datum for the third
  stage is effective.
* `CategoryTheory.Functor.isStack_stageThreeProj`: the third stage is a stack.

## Implementation notes

`CategoryTheory.Functor.HasEffectiveDescent` for `CategoryTheory.Functor.descentPairProj` is false
for a general fibred source: the plus construction of a presheaf of sets is a sheaf only when the
presheaf is separated. Hence the hypothesis on the source, which is what the first two stages of
the stackification produce.

For a 1-morphism `N` of fibred categories whose induced functors on fibres are fully faithful, a
descent datum in the target whose objects are isomorphic to images of objects of the source
descends: the gluing isomorphisms are the unique preimages of the conjugated gluing isomorphisms of
the target datum, and the cocycle condition and the base-change compatibility follow from
faithfulness.
-/

@[expose] public section

universe vb

-- The chosen pullbacks of `CategoryTheory.Functor.IsPreFibered` and the inclusion of a fibre are
-- semireducible, so the endpoints of the composites below agree only once they unfold.
set_option backward.isDefEq.respectTransparency false
universe v v₁ v₂ u₁ u₂ u₃

namespace CategoryTheory.Functor

open CategoryTheory Category

section Transport

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜] {ℬ : Type u₃}
  [Category.{v} ℬ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} [q.IsFibered] [r.IsFibered] {N : 𝒜 ⥤ ℬ}

/-! ### Base change of an isomorphism of a fibre -/

section BaseChange

variable {𝒟 : Type u₂} [Category.{v} 𝒟] {s : 𝒟 ⥤ 𝒞} [s.IsPreFibered]

end BaseChange

/-! ### Replacing the objects of a descent datum by isomorphic ones -/

/-- A descent datum transported along a family of isomorphisms of its objects. -/
noncomputable def SieveDescentDatum.transportObj {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → r.Fiber V)
    (κ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), w f hf ≅ D.obj f hf) : SieveDescentDatum r R
    where
  obj := w
  iso _ _ _ {f} hf {g} hg ε ε' heq :=
    pullbackFiberIso (κ f hf) ε ≪≫ D.iso hf hg ε ε' heq ≪≫ (pullbackFiberIso (κ g hg) ε').symm
  cocycle _ _ _ _ {f} hf {g} hg {h} hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (D.iso hf hg ε₁ ε₂ h₁₂).hom, D.cocycle hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]
  iso_pullback _ _ _ _ {f} hf {g} hg ε ε' heq γ := by
    have hD := D.iso_pullback hf hg ε ε' heq γ
    simp only [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, pullbackFiberIso_inv,
      Category.assoc, pullbackFiberHom_comp]
    rw [pullbackFiberHom_comp_base (κ f hf).hom ε γ, pullbackFiberHom_comp_base (κ g hg).inv ε' γ]
    simp only [Category.assoc]
    rw [← hD]
    simp [pullbackFiberIso_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- The objects of a transported descent datum are the given replacement objects. -/
@[simp]
theorem SieveDescentDatum.transportObj_obj {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → r.Fiber V)
    (κ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), w f hf ≅ D.obj f hf) {V : 𝒞} (f : V ⟶ U) (hf : R f) :
    (D.transportObj w κ).obj f hf = w f hf :=
  rfl

/-- The gluing isomorphisms of a transported descent datum are those of the original datum,
conjugated by the base changes of the given isomorphisms of objects. -/
theorem SieveDescentDatum.transportObj_iso {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → r.Fiber V)
    (κ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), w f hf ≅ D.obj f hf) {V W Z : 𝒞} {f : V ⟶ U} (hf : R f)
    {g : W ⟶ U} (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    ((D.transportObj w κ).iso hf hg ε ε' heq).hom =
      pullbackFiberHom (κ f hf).hom ε ≫
        (D.iso hf hg ε ε' heq).hom ≫ pullbackFiberHom (κ g hg).inv ε' := by
  simp [transportObj]

/-! ### The comparison isomorphism of a 1-morphism and iterated chosen pullbacks -/

/-- **The comparison isomorphism of a 1-morphism is compatible with the contraction of an iterated
chosen pullback.** Both sides carry the image under `N` of the chosen cartesian lift of `γ ≫ ε` to
the composite of the chosen cartesian lifts of `γ` and `ε`. -/
lemma IsFibredOneMorphism.pullbackFiberCompIso_mapPullbackFiberIso (hN : IsFibredOneMorphism q r N)
    {U : 𝒞} (a : q.Fiber U) {V Z : 𝒞} (ε : V ⟶ U) (γ : Z ⟶ V) :
    (pullbackFiberCompIso ((fiberFunctorOfCompEq hN.comp_eq U).obj a) ε γ).hom ≫
        (hN.mapPullbackFiberIso a (γ ≫ ε)).hom =
      pullbackFiberHom (hN.mapPullbackFiberIso a ε).hom γ ≫
        (hN.mapPullbackFiberIso (pullbackFiber q a ε) γ).hom ≫
        (fiberFunctorOfCompEq hN.comp_eq Z).map (pullbackFiberCompIso a ε γ).hom := by
  refine
    fiber_hom_ext_of_cartesian (γ ≫ ε) (N.map (IsPreFibered.pullbackMap a.2 (γ ≫ ε)))
      (hN.isCartesian_map_pullbackMap a (γ ≫ ε)) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map]
  rw [← Functor.map_comp N (Fiber.fiberInclusion.map (pullbackFiberCompIso a ε γ).hom),
    pullbackFiberCompIso_hom_fac, Functor.map_comp, ←
    Category.assoc (Fiber.fiberInclusion.map (hN.mapPullbackFiberIso (pullbackFiber q a ε) γ).hom),
    mapPullbackFiberIso_hom_fac hN (pullbackFiber q a ε) γ, ←
    Category.assoc
      (Fiber.fiberInclusion.map (pullbackFiberHom (hN.mapPullbackFiberIso a ε).hom γ)),
    pullbackFiberHom_fac, Category.assoc, mapPullbackFiberIso_hom_fac hN a ε,
    mapPullbackFiberIso_hom_fac hN a (γ ≫ ε), pullbackFiberCompIso_hom_fac]

/-- `CategoryTheory.Functor.IsFibredOneMorphism.pullbackFiberCompIso_mapPullbackFiberIso` solved
for the image under the fibre functor of the contraction. -/
lemma IsFibredOneMorphism.map_pullbackFiberCompIso_hom (hN : IsFibredOneMorphism q r N) {U : 𝒞}
    (a : q.Fiber U) {V Z : 𝒞} (ε : V ⟶ U) (γ : Z ⟶ V) :
    (fiberFunctorOfCompEq hN.comp_eq Z).map (pullbackFiberCompIso a ε γ).hom =
      (hN.mapPullbackFiberIso (pullbackFiber q a ε) γ).inv ≫
        pullbackFiberHom (hN.mapPullbackFiberIso a ε).inv γ ≫
        (pullbackFiberCompIso ((fiberFunctorOfCompEq hN.comp_eq U).obj a) ε γ).hom ≫
        (hN.mapPullbackFiberIso a (γ ≫ ε)).hom := by
  have hinv :
    pullbackFiberHom (hN.mapPullbackFiberIso a ε).inv γ ≫
        pullbackFiberHom (hN.mapPullbackFiberIso a ε).hom γ =
      𝟙 _ := by
    rw [← pullbackFiberHom_comp, Iso.inv_hom_id, pullbackFiberHom_id]
  rw [hN.pullbackFiberCompIso_mapPullbackFiberIso a ε γ, ←
    Category.assoc (pullbackFiberHom (hN.mapPullbackFiberIso a ε).inv γ), hinv, Category.id_comp,
    Iso.inv_hom_id_assoc]

/-- The image under the fibre functor of the contraction of an iterated chosen pullback, as an
isomorphism. -/
lemma IsFibredOneMorphism.map_pullbackFiberCompIso (hN : IsFibredOneMorphism q r N) {U : 𝒞}
    (a : q.Fiber U) {V Z : 𝒞} (ε : V ⟶ U) (γ : Z ⟶ V) :
    (fiberFunctorOfCompEq hN.comp_eq Z).mapIso (pullbackFiberCompIso a ε γ) =
      (hN.mapPullbackFiberIso (pullbackFiber q a ε) γ).symm ≪≫
        (pullbackFiberIso (hN.mapPullbackFiberIso a ε) γ).symm ≪≫
        pullbackFiberCompIso ((fiberFunctorOfCompEq hN.comp_eq U).obj a) ε γ ≪≫
        hN.mapPullbackFiberIso a (γ ≫ ε) :=
  Iso.ext (by simpa using hN.map_pullbackFiberCompIso_hom a ε γ)

/-- The image under the fibre functor of a base change is the base change of the image, conjugated
by the comparison isomorphisms. -/
lemma IsFibredOneMorphism.map_pullbackFiberHom (hN : IsFibredOneMorphism q r N) {U : 𝒞}
    {a b : q.Fiber U} (φ : a ⟶ b) {V : 𝒞} (γ : V ⟶ U) :
    (fiberFunctorOfCompEq hN.comp_eq V).map (pullbackFiberHom φ γ) =
      (hN.mapPullbackFiberIso a γ).inv ≫
        pullbackFiberHom ((fiberFunctorOfCompEq hN.comp_eq U).map φ) γ ≫
        (hN.mapPullbackFiberIso b γ).hom := by
  rw [← Category.assoc, ← mapPullbackFiberIso_naturality hN φ γ, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The isomorphism form of
`CategoryTheory.Functor.IsFibredOneMorphism.map_pullbackFiberHom`. -/
lemma IsFibredOneMorphism.map_pullbackFiberIso (hN : IsFibredOneMorphism q r N) {U : 𝒞}
    {a b : q.Fiber U} (φ : a ≅ b) {V : 𝒞} (γ : V ⟶ U) :
    (fiberFunctorOfCompEq hN.comp_eq V).mapIso (pullbackFiberIso φ γ) =
      (hN.mapPullbackFiberIso a γ).symm ≪≫
        pullbackFiberIso ((fiberFunctorOfCompEq hN.comp_eq U).mapIso φ) γ ≪≫
        hN.mapPullbackFiberIso b γ :=
  Iso.ext (by simpa using hN.map_pullbackFiberHom φ.hom γ)

/-! ### Fibrewise full faithfulness, and the isomorphisms it descends -/

/-- A 1-morphism of fibred categories over the base is *fibrewise fully faithful* when each of the
functors it induces on fibres is: two morphisms of a fibre with the same image are equal, and every
isomorphism between the images of two objects of a fibre is the image of an isomorphism.

Only isomorphisms are asked to be in the image, because that is all the descent construction below
needs, and it is what the sheaf condition on the morphism presheaves of the source provides. -/
structure IsFibredOneMorphism.IsFibrewiseFullyFaithful {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} [q.IsFibered]
    [r.IsFibered] {N : 𝒜 ⥤ ℬ} (hN : IsFibredOneMorphism q r N) : Prop where
  /-- The functor induced on each fibre is faithful. -/
  faithful :
    ∀ {V : 𝒞} {a b : q.Fiber V} (m n : a ⟶ b),
      (fiberFunctorOfCompEq hN.comp_eq V).map m = (fiberFunctorOfCompEq hN.comp_eq V).map n → m = n
  /-- Every isomorphism between the images of two objects of a fibre is the image of one. -/
  full_iso :
    ∀ {V : 𝒞} {a b : q.Fiber V}
      (e : (fiberFunctorOfCompEq hN.comp_eq V).obj a ≅ (fiberFunctorOfCompEq hN.comp_eq V).obj b),
      ∃ ι : a ≅ b, (fiberFunctorOfCompEq hN.comp_eq V).map ι.hom = e.hom

namespace IsFibredOneMorphism.IsFibrewiseFullyFaithful

/-- The isomorphism of a fibre that a fibrewise fully faithful 1-morphism descends an isomorphism
of the images to. -/
noncomputable def descendIso {hN : IsFibredOneMorphism q r N} (hff : hN.IsFibrewiseFullyFaithful)
    {V : 𝒞} {a b : q.Fiber V}
    (e : (fiberFunctorOfCompEq hN.comp_eq V).obj a ≅ (fiberFunctorOfCompEq hN.comp_eq V).obj b) :
    a ≅ b :=
  (hff.full_iso e).choose

/-- The descended isomorphism has the given isomorphism as its image. -/
@[simp]
lemma map_descendIso_hom {hN : IsFibredOneMorphism q r N} (hff : hN.IsFibrewiseFullyFaithful)
    {V : 𝒞} {a b : q.Fiber V}
    (e : (fiberFunctorOfCompEq hN.comp_eq V).obj a ≅ (fiberFunctorOfCompEq hN.comp_eq V).obj b) :
    (fiberFunctorOfCompEq hN.comp_eq V).map (hff.descendIso e).hom = e.hom :=
  (hff.full_iso e).choose_spec

/-- A morphism of a fibre is determined by its image; so the descended isomorphism is the only one
with the given image. -/
lemma descendIso_eq {hN : IsFibredOneMorphism q r N} (hff : hN.IsFibrewiseFullyFaithful) {V : 𝒞}
    {a b : q.Fiber V}
    {e : (fiberFunctorOfCompEq hN.comp_eq V).obj a ≅ (fiberFunctorOfCompEq hN.comp_eq V).obj b}
    (ι : a ≅ b) (hι : (fiberFunctorOfCompEq hN.comp_eq V).map ι.hom = e.hom) :
    ι = hff.descendIso e :=
  Iso.ext (hff.faithful _ _ (by rw [hι, hff.map_descendIso_hom]))

end IsFibredOneMorphism.IsFibrewiseFullyFaithful

/-! ### Descending a descent datum -/

/-- The datum in the target with its objects replaced by the images of the objects of the source
that they are given as isomorphic to. Its gluing isomorphisms are the conjugates of those of the
original datum, so descending it is a matter of full faithfulness alone. -/
noncomputable def SieveDescentDatum.toImage (hN : IsFibredOneMorphism q r N) {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum r R) (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → q.Fiber V)
    (κ :
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) ≅ D.obj f hf) :
    SieveDescentDatum r R :=
  D.transportObj (fun ⦃_⦄ f hf ↦ (fiberFunctorOfCompEq hN.comp_eq _).obj (w f hf)) κ

omit [q.IsFibered] in
/-- The objects of `CategoryTheory.Functor.SieveDescentDatum.toImage` are the images of the given
objects of the source. -/
@[simp]
lemma SieveDescentDatum.toImage_obj (hN : IsFibredOneMorphism q r N) {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum r R) (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → q.Fiber V)
    (κ :
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) ≅ D.obj f hf)
    {V : 𝒞} (f : V ⟶ U) (hf : R f) :
    (D.toImage hN w κ).obj f hf = (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) :=
  rfl

/-- The gluing isomorphism of the descended datum: the unique preimage of the gluing isomorphism of
the datum in the target, conjugated by the comparison isomorphisms of the 1-morphism. -/
noncomputable def SieveDescentDatum.descendAlongIso {hN : IsFibredOneMorphism q r N}
    (hff : hN.IsFibrewiseFullyFaithful) {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → q.Fiber V)
    (κ :
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) ≅ D.obj f hf)
    ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) : pullbackFiber q (w f hf) ε ≅ pullbackFiber q (w g hg) ε' :=
  hff.descendIso
    ((hN.mapPullbackFiberIso (w f hf) ε).symm ≪≫
      (D.toImage hN w κ).iso hf hg ε ε' heq ≪≫ hN.mapPullbackFiberIso (w g hg) ε')

/-- The image of a gluing isomorphism of the descended datum is the gluing isomorphism of the datum
in the target, conjugated by the comparison isomorphisms of the 1-morphism. -/
@[simp]
lemma SieveDescentDatum.map_descendAlongIso_hom {hN : IsFibredOneMorphism q r N}
    (hff : hN.IsFibrewiseFullyFaithful) {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → q.Fiber V)
    (κ :
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) ≅ D.obj f hf)
    ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) :
    (fiberFunctorOfCompEq hN.comp_eq Z).map (D.descendAlongIso hff w κ hf hg ε ε' heq).hom =
      (hN.mapPullbackFiberIso (w f hf) ε).inv ≫
        ((D.toImage hN w κ).iso hf hg ε ε' heq).hom ≫
        (hN.mapPullbackFiberIso (w g hg) ε').hom := by
  rw [descendAlongIso, hff.map_descendIso_hom]
  simp

/-- The isomorphism form of
`CategoryTheory.Functor.SieveDescentDatum.map_descendAlongIso_hom`. -/
lemma SieveDescentDatum.map_descendAlongIso {hN : IsFibredOneMorphism q r N}
    (hff : hN.IsFibrewiseFullyFaithful) {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → q.Fiber V)
    (κ :
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) ≅ D.obj f hf)
    ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) :
    (fiberFunctorOfCompEq hN.comp_eq Z).mapIso (D.descendAlongIso hff w κ hf hg ε ε' heq) =
      (hN.mapPullbackFiberIso (w f hf) ε).symm ≪≫
        (D.toImage hN w κ).iso hf hg ε ε' heq ≪≫ hN.mapPullbackFiberIso (w g hg) ε' :=
  Iso.ext (by simp)

/-- **A descent datum whose objects are the images of objects of the source descends.** The gluing
isomorphisms are the unique preimages of the conjugated gluing isomorphisms of the given datum; the
cocycle condition and the base-change compatibility follow from faithfulness. -/
noncomputable def SieveDescentDatum.descendAlong {hN : IsFibredOneMorphism q r N}
    (hff : hN.IsFibrewiseFullyFaithful) {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → q.Fiber V)
    (κ :
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) ≅ D.obj f hf) :
    SieveDescentDatum q R
    where
  obj := w
  iso _ _ _ _ hf _ hg ε ε' heq := D.descendAlongIso hff w κ hf hg ε ε' heq
  cocycle _ _ _ _ _ hf _ hg _ hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ := by
    refine hff.faithful _ _ ?_
    rw [Functor.map_comp, map_descendAlongIso_hom, map_descendAlongIso_hom,
      map_descendAlongIso_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (((D.toImage hN w κ).iso hf hg ε₁ ε₂ h₁₂).hom),
      (D.toImage hN w κ).cocycle hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]
  iso_pullback _ _ _ Z' {f} hf {g} hg ε ε' heq γ := by
    refine hff.faithful _ _ ?_
    have hpb := (D.toImage hN w κ).iso_pullback hf hg ε ε' heq γ
    rw [pullbackFiberIso_hom] at hpb
    rw [Functor.map_comp, Functor.map_comp, map_descendAlongIso_hom, ←
      Functor.mapIso_inv (fiberFunctorOfCompEq hN.comp_eq Z') (pullbackFiberCompIso (w f hf) ε γ),
      ←
      Functor.mapIso_hom (fiberFunctorOfCompEq hN.comp_eq Z') (pullbackFiberCompIso (w g hg) ε' γ),
      ←
      Functor.mapIso_hom (fiberFunctorOfCompEq hN.comp_eq Z')
        (pullbackFiberIso (D.descendAlongIso hff w κ hf hg ε ε' heq) γ),
      hN.map_pullbackFiberCompIso (w f hf) ε γ, hN.map_pullbackFiberCompIso (w g hg) ε' γ,
      hN.map_pullbackFiberIso (D.descendAlongIso hff w κ hf hg ε ε' heq) γ,
      D.map_descendAlongIso hff w κ hf hg ε ε' heq]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
      Iso.hom_inv_id_assoc, pullbackFiberIso_hom, pullbackFiberIso_inv, pullbackFiberHom_comp,
      pullbackFiberHom_hom_inv_id_assoc]
    rw [← hpb]
    simp [Category.assoc, toImage_obj]

/-- The objects of the descended datum are the given objects of the source. -/
@[simp]
lemma SieveDescentDatum.descendAlong_obj {hN : IsFibredOneMorphism q r N}
    (hff : hN.IsFibrewiseFullyFaithful) {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → q.Fiber V)
    (κ :
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) ≅ D.obj f hf)
    {V : 𝒞} (f : V ⟶ U) (hf : R f) : (D.descendAlong hff w κ).obj f hf = w f hf :=
  rfl

/-! ### The contractions of a transported and of a descended datum -/

/-- The contraction of a transported datum is the contraction of the original one, conjugated by
the transporting isomorphisms. -/
theorem SieveDescentDatum.transportObj_contract {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → r.Fiber V)
    (κ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), w f hf ≅ D.obj f hf) {V Z : 𝒞} {a : V ⟶ U} (ha : R a)
    (ε : Z ⟶ V) {b : Z ⟶ U} (hb : R b) (h : ε ≫ a = b) :
    ((D.transportObj w κ).contract ha ε hb h).hom =
      pullbackFiberHom (κ a ha).hom ε ≫ (D.contract ha ε hb h).hom ≫ (κ b hb).inv := by
  simp only [SieveDescentDatum.contract, Iso.trans_hom, transportObj_iso, transportObj_obj,
    Category.assoc]
  rw [pullbackFiberHom_id_base (κ b hb).inv]

/-- The comparison isomorphism of a 1-morphism at an identity is the contraction of the chosen
pullback along that identity. -/
lemma IsFibredOneMorphism.mapPullbackFiberIso_id (hN : IsFibredOneMorphism q r N) {U : 𝒞}
    (a : q.Fiber U) :
    (hN.mapPullbackFiberIso a (𝟙 U)).hom ≫
        (fiberFunctorOfCompEq hN.comp_eq U).map (pullbackFiberIdIso a).hom =
      (pullbackFiberIdIso ((fiberFunctorOfCompEq hN.comp_eq U).obj a)).hom := by
  refine Fiber.hom_ext ?_
  rw [Functor.map_comp, fiberInclusion_map_fiberFunctorOfCompEq_map, pullbackFiberIdIso_hom_fac,
    pullbackFiberIdIso_hom_fac, mapPullbackFiberIso_hom_fac hN a (𝟙 U)]

omit [q.IsFibered] in
/-- The contraction of the datum with the objects replaced by the images. -/
theorem SieveDescentDatum.toImage_contract (hN : IsFibredOneMorphism q r N) {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum r R) (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → q.Fiber V)
    (κ :
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) ≅ D.obj f hf)
    {V Z : 𝒞} {a : V ⟶ U} (ha : R a) (ε : Z ⟶ V) {b : Z ⟶ U} (hb : R b) (h : ε ≫ a = b) :
    ((D.toImage hN w κ).contract ha ε hb h).hom =
      pullbackFiberHom (κ a ha).hom ε ≫ (D.contract ha ε hb h).hom ≫ (κ b hb).inv :=
  D.transportObj_contract _ κ ha ε hb h

/-- **The contraction of a descended datum is the descent of the contraction.** -/
theorem SieveDescentDatum.map_descendAlong_contract {hN : IsFibredOneMorphism q r N}
    (hff : hN.IsFibrewiseFullyFaithful) {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum r R)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R f → q.Fiber V)
    (κ :
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (fiberFunctorOfCompEq hN.comp_eq V).obj (w f hf) ≅ D.obj f hf)
    {V Z : 𝒞} {a : V ⟶ U} (ha : R a) (ε : Z ⟶ V) {b : Z ⟶ U} (hb : R b) (h : ε ≫ a = b) :
    (fiberFunctorOfCompEq hN.comp_eq Z).map ((D.descendAlong hff w κ).contract ha ε hb h).hom =
      (hN.mapPullbackFiberIso (w a ha) ε).inv ≫ ((D.toImage hN w κ).contract ha ε hb h).hom := by
  simp only [SieveDescentDatum.contract, Iso.trans_hom, Functor.map_comp,
    SieveDescentDatum.descendAlong_obj, SieveDescentDatum.toImage_obj]
  rw [show
      ((D.descendAlong hff w κ).iso ha hb ε (𝟙 Z) (by rw [h, id_comp])).hom =
        (D.descendAlongIso hff w κ ha hb ε (𝟙 Z) (by rw [h, id_comp])).hom
      from rfl,
    D.map_descendAlongIso_hom hff w κ ha hb ε (𝟙 Z) (by rw [h, id_comp]), Category.assoc,
    Category.assoc, hN.mapPullbackFiberIso_id (w b hb)]

end Transport

/-! ### The 1-morphism into the third stage is fibrewise fully faithful

The morphism presheaves of the source being sheaves is exactly what makes the functors induced on
fibres by `CategoryTheory.Functor.toDescentPair` fully faithful: local injectivity and local
surjectivity of the map of morphism presheaves descend an isomorphism *locally*, and the sheaf
condition amalgamates the local descents.

The source and target share a hom universe large enough for descent data, independently
of the hom universe of the base. This is the same universe convention as in
`CategoryTheory.Functor.essImage_pullbackFiber_toStageThree` and
`CategoryTheory.Functor.isLocallyBijective_morPresheafMap_toStageThree`. -/

section ThirdStage

universe w t₁ t₂
variable {𝒞 : Type t₁} [Category.{vb} 𝒞] {𝒴 : Type t₂} [Category.{max t₁ t₂ w vb} 𝒴]
  {q : 𝒴 ⥤ 𝒞} [q.IsFibered] {J : GrothendieckTopology 𝒞}

/-- The map of morphism presheaves induced by the 1-morphism into the third stage is locally
injective and locally surjective. This is clause (1) of Stacks 02ZN for the third stage alone. -/
theorem isLocallyBijective_morPresheafMap_toDescentPair (U : 𝒞) (x y : q.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U)
        ((isFibredOneMorphism_toDescentPair q J).morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U)
        ((isFibredOneMorphism_toDescentPair q J).morPresheafMap x y) :=
  ⟨isLocallyInjective_morPresheafMap (isFibredOneMorphism_toDescentPair q J)
      (fun u v h ↦ locallyEqual_of_toDescentPair_map_eq u v h) U x y,
    isLocallySurjective_morPresheafMap (isFibredOneMorphism_toDescentPair q J)
      (fun G ↦ exists_covering_toDescentPair_map_comp G) U x y⟩

/-- **The functors induced on fibres by the 1-morphism into the third stage are faithful**, as soon
as the locally equal morphisms of the source are equal: two morphisms of a fibre with the same
image are locally equal in the source. -/
theorem faithful_fiberFunctor_toDescentPair
    (hsep : ∀ {x y : 𝒴} {a b : x ⟶ y}, q.LocallyEqual J a b → a = b) {U : 𝒞} {x y : q.Fiber U}
    (m n : x ⟶ y)
    (h :
      (fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq U).map m =
        (fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq U).map n) :
    m = n := by
  refine Fiber.hom_ext (hsep (locallyEqual_of_toDescentPair_map_eq _ _ ?_))
  have h₂ := congrArg Fiber.fiberInclusion.map h
  rwa [fiberInclusion_map_fiberFunctorOfCompEq_map,
    fiberInclusion_map_fiberFunctorOfCompEq_map] at h₂

/-- **The functors induced on fibres by the 1-morphism into the third stage are full on
isomorphisms**, as soon as the morphism presheaves of the source are sheaves and its locally equal
morphisms are equal.

Local bijectivity of the map of morphism presheaves descends the isomorphism along the members of
a covering sieve (`CategoryTheory.Functor.IsFibredOneMorphism.exists_locally_descends_iso`); the
local descents are compatible with base change because they are, by faithfulness, determined by
the isomorphism itself; and the sheaf condition amalgamates them
(`CategoryTheory.Functor.exists_fiberIso_of_locally`). That the amalgamation has the given
isomorphism as its image is separatedness of the morphisms of the third stage. -/
theorem exists_fiberIso_of_toDescentPair_iso
    (hmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y)
    (hsep : ∀ {x y : 𝒴} {a b : x ⟶ y}, q.LocallyEqual J a b → a = b) {U : 𝒞} {x y : q.Fiber U}
    (e :
      (fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq U).obj x ≅
        (fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq U).obj y) :
    ∃ ι : x ≅ y,
      (fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq U).map ι.hom =
        e.hom := by
  obtain ⟨R, hR, hspec⟩ :=
    (isFibredOneMorphism_toDescentPair q J).exists_locally_descends_iso x y
      (fun W a b ↦ isLocallyBijective_morPresheafMap_toDescentPair W a b) e
  choose t ht using hspec
  have hdet :
    ∀ ⦃W : 𝒞⦄ (b : W ⟶ U) (hb : R.arrows b) (s : pullbackFiber q x b ⟶ pullbackFiber q y b),
      (toDescentPair q J).map (Fiber.fiberInclusion.map s) ≫
            (toDescentPair q J).map (IsPreFibered.pullbackMap y.2 b) =
          (toDescentPair q J).map (IsPreFibered.pullbackMap x.2 b) ≫
            Fiber.fiberInclusion.map e.hom →
        s = (t b hb).hom := by
    intro W b hb s hs
    refine Fiber.hom_ext (hsep (locallyEqual_of_toDescentPair_map_eq _ _ ?_))
    have hcart := (isFibredOneMorphism_toDescentPair q J).isCartesian_map_pullbackMap y b
    have hs1 : q.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map s) := s.2
    have hs2 : q.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map (t b hb).hom) := (t b hb).hom.2
    have hl1 :
      (q.descentPairProj J).IsHomLift (𝟙 W)
        ((toDescentPair q J).map (Fiber.fiberInclusion.map s)) :=
      (isFibredOneMorphism_toDescentPair q J).map_isHomLift (𝟙 W) _
    have hl2 :
      (q.descentPairProj J).IsHomLift (𝟙 W)
        ((toDescentPair q J).map (Fiber.fiberInclusion.map (t b hb).hom)) :=
      (isFibredOneMorphism_toDescentPair q J).map_isHomLift (𝟙 W) _
    have := hcart
    have := hl1
    have := hl2
    exact
      IsCartesian.ext (q.descentPairProj J) b
        ((toDescentPair q J).map (IsPreFibered.pullbackMap y.2 b)) _ _ (by rw [hs, ht b hb])
  have hθ :
    ∀ ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (γ : W ⟶ V) (b : W ⟶ U) (hb : γ ≫ f = b)
      (hb' : R.arrows b),
      (t b hb').hom =
        (pullbackFiberCompIso' x f γ b hb).inv ≫
          pullbackFiberHom (t f hf).hom γ ≫ (pullbackFiberCompIso' y f γ b hb).hom := by
    intro V W f hf γ b hb hb'
    refine (hdet b hb' _ ?_).symm
    have hfac :
      Fiber.fiberInclusion.map
            ((pullbackFiberCompIso' x f γ b hb).inv ≫
              pullbackFiberHom (t f hf).hom γ ≫ (pullbackFiberCompIso' y f γ b hb).hom) ≫
          IsPreFibered.pullbackMap y.2 b =
        (Fiber.fiberInclusion.map (pullbackFiberCompIso' x f γ b hb).inv ≫
            IsPreFibered.pullbackMap (pullbackFiber q x f).2 γ) ≫
          Fiber.fiberInclusion.map (t f hf).hom ≫ IsPreFibered.pullbackMap y.2 f := by
      simp [Functor.map_comp, Category.assoc, pullbackFiberCompIso'_hom_fac,
        pullbackFiberHom_fac_assoc]
    have step :
      (toDescentPair q J).map
          (Fiber.fiberInclusion.map
              ((pullbackFiberCompIso' x f γ b hb).inv ≫
                pullbackFiberHom (t f hf).hom γ ≫ (pullbackFiberCompIso' y f γ b hb).hom) ≫
            IsPreFibered.pullbackMap y.2 b) =
        (toDescentPair q J).map (IsPreFibered.pullbackMap x.2 b) ≫
          Fiber.fiberInclusion.map e.hom := by
      rw [hfac]
      simp only [Functor.map_comp, Category.assoc]
      rw [ht f hf, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        Category.assoc, pullbackFiberCompIso'_inv_fac]
    rw [← Functor.map_comp]
    exact step
  obtain ⟨ι, hι⟩ := exists_fiberIso_of_locally q (hmor U) hR (fun {_W} b hb ↦ t b hb) hθ
  refine ⟨ι, ?_⟩
  refine
    fiber_hom_eq_of_pullbackFiberHom_locally_eq
      (fun hab ↦ (locallyEqual_descentPairProj_iff hsep _ _).mp hab) hR ?_
  intro W b hb
  rw [(isFibredOneMorphism_toDescentPair q J).pullbackFiberHom_map_eq ι.hom b, hι b hb]
  refine
    fiber_hom_ext_of_cartesian b
      (IsPreFibered.pullbackMap
        ((fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq U).obj y).2 b)
      (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map,
    IsFibredOneMorphism.mapPullbackFiberIso_inv_fac, pullbackFiberHom_fac]
  rw [ht b hb, ← Category.assoc,
    IsFibredOneMorphism.mapPullbackFiberIso_hom_fac (isFibredOneMorphism_toDescentPair q J) x b]

/-- **The 1-morphism into the third stage is fibrewise fully faithful**, as soon as the morphism
presheaves of the source are sheaves and its locally equal morphisms are equal. -/
theorem isFibrewiseFullyFaithful_toDescentPair
    (hmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y)
    (hsep : ∀ {x y : 𝒴} {a b : x ⟶ y}, q.LocallyEqual J a b → a = b) :
    (isFibredOneMorphism_toDescentPair q J).IsFibrewiseFullyFaithful
    where
  faithful _ _ h := faithful_fiberFunctor_toDescentPair hsep _ _ h
  full_iso e := exists_fiberIso_of_toDescentPair_iso hmor hsep e

end ThirdStage

/-- Precomposing a cartesian morphism with an isomorphism that lies over an identity gives a
cartesian morphism. -/
private theorem isCartesian_iso_comp_of_isHomLift {𝒮' 𝒳' : Type*} [Category 𝒮'] [Category 𝒳']
    {p' : 𝒳' ⥤ 𝒮'} {R' S' : 𝒮'} {f : R' ⟶ S'} {a' a b : 𝒳'} (e : a' ≅ a)
    (he : p'.IsHomLift (𝟙 R') e.hom) {φ : a ⟶ b} (hφ : p'.IsCartesian f φ) :
    p'.IsCartesian f (e.hom ≫ φ) := by
  have := he
  have := hφ
  infer_instance

/-! ### Descending along the contractions alone

The compatibility with the gluing isomorphisms that
`CategoryTheory.Functor.SieveDescentDatum.Descends` asks for quantifies over pairs of arrows of the
sieve and pairs of morphisms into their sources. It is equivalent to the special case in which the
second morphism is an identity — the *contraction* of the datum onto the object at the composite —
because the gluing isomorphism of two arrows is the composite of the two contractions onto the
object at their common composite
(`CategoryTheory.Functor.SieveDescentDatum.contract_hom_comp_contract_inv`). Checking the special
case is what every verification below does. -/

section IsoAlong

variable {𝒮 : Type u₁} [Category.{vb} 𝒮] {𝒳 : Type u₂} [Category.{v} 𝒳] {p : 𝒳 ⥤ 𝒮} [p.IsFibered]
  {U : 𝒮} {R : Sieve U}

/-- The contraction of a descent datum onto one of its objects is the gluing isomorphism at an
identity, which is also how
`CategoryTheory.Functor.SieveDescentDatum.isoAlong` is defined. -/
theorem SieveDescentDatum.isoAlong_eq_contract (D : SieveDescentDatum p R) ⦃V W : 𝒮⦄ {f : V ⟶ U}
    (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U} (hb : γ ≫ f = b) (hb' : R.arrows b) :
    D.isoAlong hf γ hb hb' = D.contract hf γ hb' hb :=
  rfl

/-- **A family of cartesian morphisms compatible with the contractions of a descent datum descends
it.** The gluing isomorphism of two arrows of the sieve, read at a pair of morphisms into their
sources, is the contraction onto the object at their common composite followed by the inverse of
the other contraction, so compatibility with the contractions is compatibility with all the gluing
isomorphisms. -/
theorem SieveDescentDatum.descends_of_isoAlong (D : SieveDescentDatum p R) (a : p.Fiber U)
    (ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1)
    (hcart : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), p.IsCartesian f (ζ f hf))
    (hglue :
      ∀ ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U} (hb : γ ≫ f = b)
        (hb' : R.arrows b),
        Fiber.fiberInclusion.map (D.contract hf γ hb' hb).hom ≫ ζ b hb' =
          IsPreFibered.pullbackMap (D.obj f hf).2 γ ≫ ζ f hf) :
    D.Descends p a ζ := by
  refine ⟨hcart, ?_⟩
  intro V W Z f hf g hg ε ε' heq
  have hb : R.arrows (ε ≫ f) := R.downward_closed hf ε
  have h₁ := hglue hf ε (b := ε ≫ f) rfl hb
  have h₂ := hglue hg ε' (b := ε ≫ f) heq.symm hb
  rw [← h₂, ← h₁, ← D.contract_hom_comp_contract_inv hf hg ε ε' hb rfl heq.symm heq,
    Functor.map_comp, Category.assoc, ←
    Category.assoc (Fiber.fiberInclusion.map (D.contract hg ε' hb heq.symm).inv), ←
    Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

/-- **A descent datum is effective as soon as some object of the fibre identifies its chosen
pullbacks with the objects of the datum, compatibly with the contractions.** This is the form of
effectiveness that the sheaf condition on the morphism presheaves produces, since it asks for
isomorphisms of fibres rather than for cartesian morphisms of the total category. -/
theorem SieveDescentDatum.isEffective_of_fiberIso (D : SieveDescentDatum p R) (a : p.Fiber U)
    (θ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), pullbackFiber p a f ≅ D.obj f hf)
    (hθ :
      ∀ ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U} (hb : γ ≫ f = b)
        (hb' : R.arrows b),
        θ b hb' =
          (pullbackFiberCompIso' a f γ b hb).symm ≪≫
            pullbackFiberIso (θ f hf) γ ≪≫ D.contract hf γ hb' hb) :
    D.IsEffective := by
  have hcart :
    ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f),
      p.IsCartesian f
        (Fiber.fiberInclusion.map (θ f hf).inv ≫ IsPreFibered.pullbackMap a.2 f) := by
    intro V f hf
    exact isCartesian_iso_comp_of_isHomLift (Fiber.fiberInclusion.mapIso (θ f hf)).symm
      (θ f hf).inv.2 (IsPreFibered.pullbackMap.IsCartesian _ _)
  refine
    ⟨a, fun {_V} f hf ↦ Fiber.fiberInclusion.map (θ f hf).inv ≫ IsPreFibered.pullbackMap a.2 f,
      D.descends_of_isoAlong a _ hcart ?_⟩
  intro V W f hf γ b hb hb'
  have hinv :
    (θ b hb').inv =
      (D.contract hf γ hb' hb).inv ≫
        pullbackFiberHom (θ f hf).inv γ ≫ (pullbackFiberCompIso' a f γ b hb).hom := by
    rw [hθ hf γ hb hb']
    simp
  rw [hinv, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ←
    Category.assoc (Fiber.fiberInclusion.map (D.contract hf γ hb' hb).hom), ← Functor.map_comp,
    Iso.hom_inv_id, Functor.map_id, Category.id_comp, pullbackFiberCompIso'_hom_fac, ←
    Category.assoc, pullbackFiberHom_fac, Category.assoc]

/-! ### Effectiveness of a descent datum is local on the base

A descent datum whose restriction to a covering refinement is effective is itself effective, as
soon as the morphism presheaves are sheaves: the comparisons of the chosen pullbacks of the
descended object with the objects of the datum are given over the refinement and glue. -/

section Locality

variable {J : GrothendieckTopology 𝒮}

/-- The comparison of the chosen pullback of an object a datum descends to with the object of the
datum at a composite, factored through the comparison at the arrow itself. -/
theorem SieveDescentDatum.descendsIso_factor {D : SieveDescentDatum p R} {a : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1} (hζ : D.Descends p a ζ)
    ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U} (hb : γ ≫ f = b)
    (hb' : R.arrows b) :
    SieveDescentDatum.descendsIso hζ b hb' =
      (pullbackFiberCompIso' a f γ b hb).symm ≪≫
        pullbackFiberIso (SieveDescentDatum.descendsIso hζ f hf) γ ≪≫ D.isoAlong hf γ hb hb' := by
  refine Iso.ext (fiber_hom_ext_of_cartesian b (ζ b hb') (hζ.1 b hb') _ _ ?_)
  simp [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp, Category.assoc,
    SieveDescentDatum.isoAlong_comp hζ hf γ hb hb', pullbackFiberHom_fac_assoc,
    SieveDescentDatum.descendsIso_hom_fac, pullbackFiberCompIso'_inv_fac]

variable {T : Sieve U}

/-- The comparison, over an arrow `c` of the refinement pulled back along `f`, of the chosen
pullback of the descended object along `f` with the object of the datum at `f`. -/
noncomputable def SieveDescentDatum.restrictIsoAt {D : SieveDescentDatum p R} (hT : T ≤ R)
    {a : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒮⦄ (t : V ⟶ U) (ht : T.arrows t), ((D.restrict hT).obj t ht).1 ⟶ a.1}
    (hζ : (D.restrict hT).Descends p a ζ) ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (c : W ⟶ V)
    (hc : T.arrows (c ≫ f)) :
    pullbackFiber p (pullbackFiber p a f) c ≅ pullbackFiber p (D.obj f hf) c :=
  pullbackFiberCompIso a f c ≪≫
    SieveDescentDatum.descendsIso hζ (c ≫ f) hc ≪≫ (D.contract hf c (hT _ hc) rfl).symm

/-- The local comparison, read at a *named* arrow that the composite equals. -/
theorem SieveDescentDatum.restrictIsoAt_eq {D : SieveDescentDatum p R} (hT : T ≤ R) {a : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒮⦄ (t : V ⟶ U) (ht : T.arrows t), ((D.restrict hT).obj t ht).1 ⟶ a.1}
    (hζ : (D.restrict hT).Descends p a ζ) ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (c : W ⟶ V)
    (hc : T.arrows (c ≫ f)) {t : W ⟶ U} (hct : c ≫ f = t) (ht : T.arrows t) :
    (D.restrictIsoAt hT hζ hf c hc).hom =
      (pullbackFiberCompIso' a f c t hct).hom ≫
        (SieveDescentDatum.descendsIso hζ t ht).hom ≫ (D.contract hf c (hT _ ht) hct).inv := by
  subst hct
  rfl

/-- The local comparisons are compatible with base change. -/
theorem SieveDescentDatum.restrictIsoAt_compat {D : SieveDescentDatum p R} (hT : T ≤ R)
    {a : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒮⦄ (t : V ⟶ U) (ht : T.arrows t), ((D.restrict hT).obj t ht).1 ⟶ a.1}
    (hζ : (D.restrict hT).Descends p a ζ) ⦃V : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) ⦃W W' : 𝒮⦄
    (c : W ⟶ V) (hc : T.arrows (c ≫ f)) (δ : W' ⟶ W) {c' : W' ⟶ V} (hδ : δ ≫ c = c')
    (hc' : T.arrows (c' ≫ f)) :
    (D.restrictIsoAt hT hζ hf c' hc').hom =
      (pullbackFiberCompIso' (pullbackFiber p a f) c δ c' hδ).inv ≫
        pullbackFiberHom (D.restrictIsoAt hT hζ hf c hc).hom δ ≫
        (pullbackFiberCompIso' (D.obj f hf) c δ c' hδ).hom := by
  subst hδ
  have hbf : δ ≫ (c ≫ f) = (δ ≫ c) ≫ f := (assoc δ c f).symm
  have hcinv := D.pullbackFiberHom_contract_inv_comp hf c (hT _ hc) rfl δ
  have hp2 :
    (pullbackFiberCompIso (pullbackFiber p a f) c δ).inv ≫
        pullbackFiberHom (pullbackFiberCompIso a f c).hom δ =
      (pullbackFiberCompIso a f (δ ≫ c)).hom ≫
        (pullbackFiberCompIso' a (c ≫ f) δ ((δ ≫ c) ≫ f) hbf).inv := by
    have h := pullbackFiberCompIso'_pentagon a f c δ (c ≫ f) rfl (δ ≫ c) rfl ((δ ≫ c) ≫ f) rfl
    simp only [pullbackFiberCompIso'_rfl] at h
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hf2 :
    (pullbackFiberCompIso' a (c ≫ f) δ ((δ ≫ c) ≫ f) hbf).inv ≫
        pullbackFiberHom (SieveDescentDatum.descendsIso hζ (c ≫ f) hc).hom δ =
      (SieveDescentDatum.descendsIso hζ ((δ ≫ c) ≫ f) hc').hom ≫
        ((D.restrict hT).isoAlong hc δ hbf hc').inv := by
    have h := congrArg Iso.hom ((D.restrict hT).descendsIso_factor hζ hc δ hbf hc')
    simp only [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom] at h
    rw [h]
    simp
  have hcoI :
    D.iso hf (hT _ hc) (δ ≫ c) δ (by rw [assoc]) ≪≫ (D.restrict hT).isoAlong hc δ hbf hc' =
      D.contract hf (δ ≫ c) (hT _ hc') rfl := by
    refine Iso.ext ?_
    simp only [Iso.trans_hom, SieveDescentDatum.isoAlong, SieveDescentDatum.contract]
    simp only [← Category.assoc]
    rw [D.cocycle hf (hT _ hc) (hT _ hc') (δ ≫ c) δ (𝟙 W') (by rw [assoc])
        (by
          rw [id_comp]; exact hbf)
        (by rw [id_comp])]
  have hcoinv :
    ((D.restrict hT).isoAlong hc δ hbf hc').inv ≫
        (D.iso hf (hT _ hc) (δ ≫ c) δ (by rw [assoc])).inv =
      (D.contract hf (δ ≫ c) (hT _ hc') rfl).inv := by
    rw [← hcoI]
    simp [Iso.trans_inv]
  refine Eq.symm ?_
  simp only [SieveDescentDatum.restrictIsoAt, Iso.trans_hom, Iso.symm_hom,
    pullbackFiberCompIso'_rfl, pullbackFiberHom_comp, Category.assoc]
  rw [hcinv, reassoc_of% hp2, reassoc_of% hf2, hcoinv]

/-- **Effectiveness of a descent datum is local on the base.** -/
theorem SieveDescentDatum.isEffective_of_restrict
    (hmor : ∀ (V : 𝒮) (x y : p.Fiber V), IsMorSheaf p J V x y) (D : SieveDescentDatum p R)
    (hT : T ≤ R) (hTmem : T ∈ J U) (heff : (D.restrict hT).IsEffective) : D.IsEffective := by
  obtain ⟨a, ζ, hζ⟩ := heff
  have hζ' : (D.restrict hT).Descends p a ζ := hζ
  have hex :
    ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f),
      ∃ θ : pullbackFiber p a f ≅ D.obj f hf,
        ∀ ⦃W : 𝒮⦄ (c : W ⟶ V) (hc : (T.pullback f).arrows c),
          pullbackFiberHom θ.hom c = (D.restrictIsoAt hT hζ' hf c hc).hom := by
    intro V f hf
    refine
      exists_fiberIso_of_locally p (hmor V) (J.pullback_stable f hTmem)
        (fun {_W} c hc ↦ D.restrictIsoAt hT hζ' hf c hc) ?_
    intro W W' c hc δ c' hδ hc'
    exact D.restrictIsoAt_compat hT hζ' hf c hc δ hδ hc'
  choose θ hθloc using hex
  refine D.isEffective_of_fiberIso a θ ?_
  intro V W f hf γ b hb hb'
  refine Iso.ext ?_
  refine eq_of_pullbackFiberHom_locally_eq p (hmor W _ _) (J.pullback_stable b hTmem) ?_
  intro W' e he
  have heb : T.arrows (e ≫ b) := he
  have hegf : (e ≫ γ) ≫ f = e ≫ b := by rw [assoc, hb]
  have hegfT : (T.pullback f).arrows (e ≫ γ) := by
    rw [Sieve.pullback_apply]
    rw [hegf]; exact heb
  have hA :
    pullbackFiberHom (pullbackFiberCompIso' a f γ b hb).inv e ≫
        (pullbackFiberCompIso (pullbackFiber p a f) γ e).hom ≫
        (pullbackFiberCompIso' a f (e ≫ γ) (e ≫ b) hegf).hom =
      (pullbackFiberCompIso' a b e (e ≫ b) rfl).hom := by
    have h := pullbackFiberCompIso'_pentagon a f γ e b hb (e ≫ γ) rfl (e ≫ b) hegf
    simp only [pullbackFiberCompIso'_rfl] at h
    rw [← h, ← Category.assoc]
    simp
  have hciv := D.pullbackFiberHom_contract_inv_comp hf γ hb' hb e
  have h2 :
    pullbackFiberHom (D.contract hf γ hb' hb).hom e =
      (pullbackFiberCompIso (D.obj f hf) γ e).hom ≫
        (D.iso hf hb' (e ≫ γ) e (by rw [assoc, hb])).hom := by
    rw [← pullbackFiberIso_inv (D.contract hf γ hb' hb) e, Iso.inv_comp_eq] at hciv
    rw [← pullbackFiberIso_hom (D.contract hf γ hb' hb) e, hciv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hB0 :
    (D.iso hf hb' (e ≫ γ) e (by rw [assoc, hb])).hom ≫ (D.contract hb' e (hT _ heb) rfl).hom =
      (D.contract hf (e ≫ γ) (hT _ heb) hegf).hom := by
    simp only [SieveDescentDatum.contract, Iso.trans_hom]
    simp only [← Category.assoc]
    rw [D.cocycle hf hb' (hT _ heb) (e ≫ γ) e (𝟙 W') (by rw [assoc, hb]) (by rw [id_comp])
        (by
          rw [id_comp]; exact hegf)]
  have hB :
    (D.contract hf (e ≫ γ) (hT _ heb) hegf).inv ≫
        (pullbackFiberCompIso (D.obj f hf) γ e).inv ≫
        pullbackFiberHom (D.contract hf γ hb' hb).hom e =
      (D.contract hb' e (hT _ heb) rfl).inv := by
    rw [h2, Iso.inv_hom_id_assoc, Iso.inv_comp_eq, ← hB0]
    simp
  have hstep :
    pullbackFiberHom (pullbackFiberHom (θ f hf).hom γ) e =
      (pullbackFiberCompIso (pullbackFiber p a f) γ e).hom ≫
        pullbackFiberHom (θ f hf).hom (e ≫ γ) ≫ (pullbackFiberCompIso (D.obj f hf) γ e).inv := by
    rw [pullbackFiberHom_comp_base (θ f hf).hom γ e]
    simp
  rw [hθloc b hb' e he, D.restrictIsoAt_eq hT hζ' hb' e he rfl heb]
  simp only [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, pullbackFiberHom_comp]
  rw [hstep, hθloc f hf (e ≫ γ) hegfT, D.restrictIsoAt_eq hT hζ' hf (e ≫ γ) hegfT hegf heb]
  simp only [Category.assoc]
  rw [reassoc_of% hA, hB]

end Locality

end IsoAlong

/-! ### A descent pair descends its own datum

The third stage adjoins the object a descent datum prescribes by declaring the pair `(R, D)` to
*be* that object. What that means precisely is proved here: the descent pair `A` carries, for each
arrow `g` of its covering sieve, a morphism over `g` from the descent pair of the object `A.datum`
attaches to `g`, this morphism is cartesian, and the family is compatible with the contractions of
`A.datum` — so `A` descends the image of its own datum in the third stage.

Everything is phrased with `CategoryTheory.Functor.DescentPair.ofFiber`, which records the object
of the base literally, rather than with `CategoryTheory.Functor.DescentPair.ofObj`; the two pairs
are equal but not definitionally so, and using the first keeps every statement below free of
transports. -/

section SelfDescent

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒮} [p.IsFibered]

/-- The morphism of chosen pullbacks induced by a morphism `φ : x.1 ⟶ y.1` of `𝒳` lying over
`k : V ⟶ V'`: the unique morphism from the chosen pullback of `x` along `δ` to the chosen pullback
of `y` along an arrow `l` that `δ ≫ k` equals whose composite with the chosen cartesian lift of `l`
is the chosen cartesian lift of `δ` followed by `φ`. -/
noncomputable def pullbackFiberOfFiberHom {V V' : 𝒮} {x : p.Fiber V} {y : p.Fiber V'}
    (φ : x.1 ⟶ y.1) {k : V ⟶ V'} (hφ : p.IsHomLift k φ) {W : 𝒮} (δ : W ⟶ V) {l : W ⟶ V'}
    (h : δ ≫ k = l) : pullbackFiber p x δ ⟶ pullbackFiber p y l :=
  have := hφ
  have hlift : p.IsHomLift l (IsPreFibered.pullbackMap x.2 δ ≫ φ) := by
    have h0 : p.IsHomLift (δ ≫ k) (IsPreFibered.pullbackMap x.2 δ ≫ φ) := inferInstance
    rwa [h] at h0
  have := hlift
  ⟨IsCartesian.map p l (IsPreFibered.pullbackMap y.2 l) (IsPreFibered.pullbackMap x.2 δ ≫ φ),
    IsCartesian.map_isHomLift p l _ _⟩

/-- The equation that determines `CategoryTheory.Functor.pullbackFiberOfFiberHom`. -/
@[reassoc (attr := simp)]
theorem pullbackFiberOfFiberHom_fac {V V' : 𝒮} {x : p.Fiber V} {y : p.Fiber V'} (φ : x.1 ⟶ y.1)
    {k : V ⟶ V'} (hφ : p.IsHomLift k φ) {W : 𝒮} (δ : W ⟶ V) {l : W ⟶ V'} (h : δ ≫ k = l) :
    Fiber.fiberInclusion.map (pullbackFiberOfFiberHom φ hφ δ h) ≫ IsPreFibered.pullbackMap y.2 l =
      IsPreFibered.pullbackMap x.2 δ ≫ φ :=
  have := hφ
  have hlift : p.IsHomLift l (IsPreFibered.pullbackMap x.2 δ ≫ φ) := by
    have h0 : p.IsHomLift (δ ≫ k) (IsPreFibered.pullbackMap x.2 δ ≫ φ) := inferInstance
    rwa [h] at h0
  have := hlift
  IsCartesian.fac p l (IsPreFibered.pullbackMap y.2 l) (IsPreFibered.pullbackMap x.2 δ ≫ φ)

/-- For a morphism of the fibre, `CategoryTheory.Functor.pullbackFiberOfFiberHom` is base change,
followed by the comparison of the chosen pullbacks along `δ` and `δ ≫ 𝟙`. -/
theorem pullbackFiberOfFiberHom_eq_pullbackFiberHom {V : 𝒮} {x y : p.Fiber V} (m : x ⟶ y) {W : 𝒮}
    (δ : W ⟶ V) {l : W ⟶ V} (h : δ ≫ 𝟙 V = l) :
    pullbackFiberOfFiberHom (Fiber.fiberInclusion.map m) m.2 δ h =
      pullbackFiberHom m δ ≫ (pullbackFiberCongr y ((comp_id δ).symm.trans h)).hom := by
  refine
    fiber_hom_ext_of_cartesian l (IsPreFibered.pullbackMap y.2 l)
      (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp [Functor.map_comp, Category.assoc, pullbackFiberCongr_hom_fac,
    pullbackFiberOfFiberHom_fac, pullbackFiberHom_fac]

/-- For a chosen cartesian lift, `CategoryTheory.Functor.pullbackFiberOfFiberHom` is the
contraction of the iterated chosen pullback. -/
theorem pullbackFiberOfFiberHom_pullbackMap {V V' : 𝒮} (y : p.Fiber V') (γ : V ⟶ V') {W : 𝒮}
    (δ : W ⟶ V) {l : W ⟶ V'} (h : δ ≫ γ = l) :
    pullbackFiberOfFiberHom (IsPreFibered.pullbackMap y.2 γ) inferInstance δ h =
      (pullbackFiberCompIso' y γ δ l h).hom := by
  refine
    fiber_hom_ext_of_cartesian l (IsPreFibered.pullbackMap y.2 l)
      (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  rw [pullbackFiberOfFiberHom_fac, pullbackFiberCompIso'_hom_fac]

variable {J : GrothendieckTopology 𝒮}

/-- A morphism of `𝒳` between the underlying objects of two objects of fibres, read as a morphism
datum of their descent pairs. -/
noncomputable def DescentPairData.ofFiberHom (J : GrothendieckTopology 𝒮) {V V' : 𝒮}
    {x : p.Fiber V} {y : p.Fiber V'} (φ : x.1 ⟶ y.1) {k : V ⟶ V'} (hφ : p.IsHomLift k φ) :
    DescentPairData (DescentPair.ofFiber x J) (DescentPair.ofFiber y J)
    where
  base := k
  hom :=
    { sieve := ⊤
      sieve_mem := J.top_mem V
      le_dom := le_refl _
      mem_cod := fun _ _ _ ↦ trivial
      map := fun _ δ _ _ _ h ↦ pullbackFiberOfFiberHom φ hφ δ h
      map_glue := fun _ _ _ δ _ δ' _ _ _ h _ _ h' ε ε' heq ↦ by
        subst h
        subst h'
        have hc :
          p.IsCartesian (ε' ≫ (δ' ≫ k))
            (IsPreFibered.pullbackMap (pullbackFiber p y (δ' ≫ k)).2 ε' ≫
              IsPreFibered.pullbackMap y.2 (δ' ≫ k)) :=
          inferInstance
        refine fiber_hom_ext_of_cartesian (ε' ≫ (δ' ≫ k)) _ hc _ _ ?_
        simp [SieveDescentDatum.ofFiber_iso, Functor.map_comp, Category.assoc,
          pullbackFiberComparison_hom_fac, pullbackFiberComparison_hom_fac_assoc,
          pullbackFiberHom_fac_assoc, pullbackFiberOfFiberHom_fac] }

/-- The base of `CategoryTheory.Functor.DescentPairData.ofFiberHom J φ hφ` is the morphism `k`
that `φ` lies over. -/
@[simp]
theorem DescentPairData.ofFiberHom_base (J : GrothendieckTopology 𝒮) {V V' : 𝒮} {x : p.Fiber V}
    {y : p.Fiber V'} (φ : x.1 ⟶ y.1) {k : V ⟶ V'} (hφ : p.IsHomLift k φ) :
    (DescentPairData.ofFiberHom J φ hφ).base = k :=
  rfl

/-- The morphism that `CategoryTheory.Functor.DescentPairData.ofFiberHom J φ hφ` attaches to an
arrow `δ` is the morphism of chosen pullbacks induced by `φ`. -/
@[simp]
theorem DescentPairData.ofFiberHom_hom_map (J : GrothendieckTopology 𝒮) {V V' : 𝒮} {x : p.Fiber V}
    {y : p.Fiber V'} (φ : x.1 ⟶ y.1) {k : V ⟶ V'} (hφ : p.IsHomLift k φ) {W : 𝒮} (δ : W ⟶ V)
    (hδ : (⊤ : Sieve V).arrows δ) {l : W ⟶ V'} (hl : (⊤ : Sieve V').arrows l) (h : δ ≫ k = l) :
    (DescentPairData.ofFiberHom J φ hφ).hom.map δ hδ hl h = pullbackFiberOfFiberHom φ hφ δ h :=
  rfl

/-- A morphism of `𝒳` between the underlying objects of two objects of fibres, read as a morphism
of their descent pairs. -/
noncomputable def ofFiberMor (J : GrothendieckTopology 𝒮) {V V' : 𝒮} {x : p.Fiber V}
    {y : p.Fiber V'} (φ : x.1 ⟶ y.1) {k : V ⟶ V'} (hφ : p.IsHomLift k φ) :
    DescentPair.ofFiber x J ⟶ DescentPair.ofFiber y J :=
  DescentMor.mk (DescentPairData.ofFiberHom J φ hφ)

/-- `CategoryTheory.Functor.ofFiberMor J φ hφ` lies over the morphism `k` that `φ` lies over. -/
theorem isHomLift_ofFiberMor (J : GrothendieckTopology 𝒮) {V V' : 𝒮} {x : p.Fiber V}
    {y : p.Fiber V'} (φ : x.1 ⟶ y.1) {k : V ⟶ V'} (hφ : p.IsHomLift k φ) :
    (p.descentPairProj J).IsHomLift k (ofFiberMor J φ hφ) :=
  DescentMor.isHomLift_mk (DescentPairData.ofFiberHom J φ hφ)

/-! #### The canonical morphism from the pair of an object of the datum -/

/-- **The canonical morphism from the descent pair of the object that `A` attaches to an arrow of
its covering sieve, to `A` itself.** It is the contraction isomorphism
`CategoryTheory.Functor.DescentPair.contractIso` followed by the canonical morphism from the
pullback, and it lies over that arrow. -/
noncomputable def DescentPair.datumHom (A : DescentPair p J) {V : 𝒮} (g : V ⟶ A.pt)
    (hg : A.sieve.arrows g) : DescentPair.ofFiber (A.datum.obj g hg) J ⟶ A :=
  (A.contractIso g hg).hom ≫ DescentMor.mk (DescentPairData.pullbackHom A g)

/-- **The canonical morphism from the pair of an object of the datum is cartesian.** -/
theorem isCartesian_datumHom (A : DescentPair p J) {V : 𝒮} (g : V ⟶ A.pt) (hg : A.sieve.arrows g) :
    (p.descentPairProj J).IsCartesian g (A.datumHom g hg) := by
  have := isStronglyCartesian_pullbackHom A g
  exact isCartesian_iso_comp_of_isHomLift (A.contractIso g hg) (isHomLift_contractIso_hom A g hg)
    inferInstance

/-- The morphism datum of `CategoryTheory.Functor.DescentPair.datumHom`. -/
noncomputable def DescentPair.datumHomData (A : DescentPair p J) {V : 𝒮} (g : V ⟶ A.pt)
    (hg : A.sieve.arrows g) : DescentPairData (DescentPair.ofFiber (A.datum.obj g hg) J) A :=
  (DescentPairData.ofContract A g hg).comp (DescentPairData.pullbackHom A g)

/-- `CategoryTheory.Functor.DescentPair.datumHom` is the class of the morphism datum
`CategoryTheory.Functor.DescentPair.datumHomData`. -/
theorem DescentPair.datumHom_eq_mk (A : DescentPair p J) {V : 𝒮} (g : V ⟶ A.pt)
    (hg : A.sieve.arrows g) : A.datumHom g hg = DescentMor.mk (A.datumHomData g hg) :=
  rfl

/-- The base of `CategoryTheory.Functor.DescentPair.datumHomData A g hg` is `𝟙 V ≫ g`. -/
@[simp]
theorem DescentPair.datumHomData_base (A : DescentPair p J) {V : 𝒮} (g : V ⟶ A.pt)
    (hg : A.sieve.arrows g) : (A.datumHomData g hg).base = 𝟙 V ≫ g :=
  rfl

/-- **The morphism the canonical morphism attaches to an arrow of the covering sieve is the
contraction of the datum onto the object at the composite.** -/
theorem DescentPair.datumHomData_hom_map (A : DescentPair p J) {V : 𝒮} (g : V ⟶ A.pt)
    (hg : A.sieve.arrows g) {W₀ : 𝒮} (δ : W₀ ⟶ V) (hδ : (A.datumHomData g hg).hom.sieve.arrows δ)
    {k : W₀ ⟶ A.pt} (hk : A.sieve.arrows k) (h : δ ≫ (A.datumHomData g hg).base = k)
    (h₁ : δ ≫ g = k) :
    (A.datumHomData g hg).hom.map δ hδ hk h = (A.datum.contract hg δ hk h₁).hom := by
  have h₀ : (δ ≫ 𝟙 V) ≫ g = k := by
    rw [comp_id]; exact h₁
  have h₂ :
    (δ ≫ (DescentPairData.ofContract A g hg).base) ≫ (DescentPairData.pullbackHom A g).base = k :=
    h₀
  refine
    Eq.trans
      (DescentPairData.comp_hom_map (DescentPairData.ofContract A g hg)
        (DescentPairData.pullbackHom A g) δ hδ.1 hδ.2 hk h₂ hδ h)
      ?_
  exact
    A.datum.contract_hom_congr_tgt hg δ ((DescentPairData.ofContract A g hg).hom.mem_cod δ hδ.1) hk
      (show δ ≫ g = (δ ≫ 𝟙 V) ≫ g by rw [comp_id]) h₁
      (A.datum.obj_congr (show (δ ≫ 𝟙 V) ≫ g = k from h₀) _ hk)

/-- The morphism that the composite of `CategoryTheory.Functor.DescentPairData.ofFiberHom J φ hφ`
with `CategoryTheory.Functor.DescentPair.datumHomData A g hg` attaches to an arrow `δ` is the
morphism of chosen pullbacks induced by `φ`, followed by the contraction of the datum of `A`. -/
theorem DescentPair.ofFiberHom_comp_datumHomData_hom_map (A : DescentPair p J) {V V₀ : 𝒮}
    {x : p.Fiber V₀} {g : V ⟶ A.pt} (hg : A.sieve.arrows g) (φ : x.1 ⟶ (A.datum.obj g hg).1)
    {c : V₀ ⟶ V} (hφ : p.IsHomLift c φ) {W₀ : 𝒮} (δ : W₀ ⟶ V₀)
    (hδ : ((DescentPairData.ofFiberHom J φ hφ).comp (A.datumHomData g hg)).hom.sieve.arrows δ)
    {k : W₀ ⟶ A.pt} (hk : A.sieve.arrows k)
    (h : δ ≫ ((DescentPairData.ofFiberHom J φ hφ).comp (A.datumHomData g hg)).base = k)
    (h₁ : (δ ≫ c) ≫ g = k) :
    ((DescentPairData.ofFiberHom J φ hφ).comp (A.datumHomData g hg)).hom.map δ hδ hk h =
      pullbackFiberOfFiberHom φ hφ δ (l := δ ≫ c) rfl ≫
        (A.datum.contract hg (δ ≫ c) hk h₁).hom := by
  have h₂ : (δ ≫ (DescentPairData.ofFiberHom J φ hφ).base) ≫ (A.datumHomData g hg).base = k :=
    show (δ ≫ c) ≫ (𝟙 V ≫ g) = k by
      rw [id_comp]; exact h₁
  refine
    Eq.trans
      (DescentPairData.comp_hom_map (DescentPairData.ofFiberHom J φ hφ) (A.datumHomData g hg) δ
        trivial hδ.2 hk h₂ hδ h)
      ?_
  rw [A.datumHomData_hom_map g hg (δ ≫ (DescentPairData.ofFiberHom J φ hφ).base) hδ.2 hk h₂ h₁]
  rfl

/-- **The canonical morphisms from the pairs of the objects of a descent datum are compatible with
its contractions.** This is the precise sense in which the third stage makes the datum of a descent
pair effective: the pair `A` *is* the object the datum prescribes. -/
theorem DescentPair.ofFiberMor_contract_comp_datumHom (A : DescentPair p J) {V W : 𝒮}
    {g : V ⟶ A.pt} (hg : A.sieve.arrows g) (γ : W ⟶ V) {b : W ⟶ A.pt} (hb : A.sieve.arrows b)
    (hγ : γ ≫ g = b) :
    ofFiberMor J (Fiber.fiberInclusion.map (A.datum.contract hg γ hb hγ).hom)
          (A.datum.contract hg γ hb hγ).hom.2 ≫
        A.datumHom b hb =
      ofFiberMor J (IsPreFibered.pullbackMap (A.datum.obj g hg).2 γ) (k := γ) inferInstance ≫
        A.datumHom g hg := by
  rw [DescentPair.datumHom_eq_mk, DescentPair.datumHom_eq_mk, ofFiberMor, ofFiberMor]
  refine (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree (by simpa using hγ.symm) ?_)
  intro W₀ δ hδ hδ' k hk h h'
  have hk₁ : δ ≫ 𝟙 W ≫ b = k := by simpa using h
  have hk₂ : (δ ≫ γ) ≫ g = k := by simpa [hγ] using h
  rw [A.ofFiberHom_comp_datumHomData_hom_map hb _ _ δ hδ hk h (by simpa using hk₁),
    A.ofFiberHom_comp_datumHomData_hom_map hg _ _ δ hδ' hk h' hk₂,
    pullbackFiberOfFiberHom_eq_pullbackFiberHom, pullbackFiberOfFiberHom_pullbackMap]
  have hk₃ : δ ≫ b = k := by rw [← hk₁, id_comp]
  have hk₄ : (δ ≫ 𝟙 W) ≫ b = k := by
    rw [comp_id]; exact hk₃
  rw [Category.assoc, ← A.datum.contract_congr hb (comp_id δ).symm hk hk₃ hk₄,
    A.datum.pullbackFiberHom_contract hg γ hb hγ δ, pullbackFiberCompIso'_rfl, Category.assoc]
  refine congrArg (fun t ↦ (pullbackFiberCompIso (A.datum.obj g hg) γ δ).hom ≫ t) ?_
  simp only [SieveDescentDatum.contract, Iso.trans_hom]
  rw [← Category.assoc,
    A.datum.cocycle hg hb hk (δ ≫ γ) δ (𝟙 W₀) (by rw [assoc, hγ])
      (by
        rw [id_comp]; exact hk₃)
      (by
        rw [id_comp, assoc, hγ]; exact hk₃)]

/-! #### Reading the canonical morphism on the pair of the underlying object

`CategoryTheory.Functor.DescentPair.ofFiber` and `CategoryTheory.Functor.DescentPair.ofObj` give
the same pair, but not definitionally, and the 1-morphism
`CategoryTheory.Functor.toDescentPair` is defined with the second. The transport between them is
confined to the three statements below. -/

/-- The transport between the two spellings of the descent pair of an object of a fibre lies over
the identity. -/
theorem isHomLift_eqToHom_ofFiber (J : GrothendieckTopology 𝒮) {V : 𝒮} (x : p.Fiber V) :
    (p.descentPairProj J).IsHomLift (𝟙 V)
      (eqToHom (DescentPair.ofFiber_eq_ofObj x J).symm :
        DescentPair.ofObj p J x.1 ⟶ DescentPair.ofFiber x J) := by
  obtain ⟨x₀, rfl⟩ := x
  exact IsHomLift.id rfl

/-- **`CategoryTheory.Functor.ofFiberMor` is the image under
`CategoryTheory.Functor.toDescentPair`**, read through the transport between the two spellings of
the descent pair of an object of a fibre. -/
theorem eqToHom_comp_ofFiberMor (J : GrothendieckTopology 𝒮) {V V' : 𝒮} {x : p.Fiber V}
    {y : p.Fiber V'} (φ : x.1 ⟶ y.1) {k : V ⟶ V'} (hφ : p.IsHomLift k φ) :
    eqToHom (DescentPair.ofFiber_eq_ofObj x J).symm ≫ ofFiberMor J φ hφ =
      (toDescentPair p J).map φ ≫ eqToHom (DescentPair.ofFiber_eq_ofObj y J).symm := by
  obtain ⟨x₀, rfl⟩ := x
  obtain ⟨y₀, rfl⟩ := y
  obtain rfl : k = p.map φ := by
    have := hφ
    simpa using (IsHomLift.fac' p k φ).symm
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  refine (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree rfl ?_)
  intro W₀ δ hδ hδ' l hl h h'
  refine
    fiber_hom_ext_of_cartesian l (IsPreFibered.pullbackMap (fiberSelf p y₀).2 l)
      (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  rw [show (DescentPairData.ofFiberHom J φ hφ).hom.map δ hδ hl h = pullbackFiberOfFiberHom φ hφ δ h
      from rfl,
    show
      (DescentPairData.ofHom (p := p) (J := J) φ).hom.map δ hδ' hl h' = pullbackFiberOfHom φ δ l h'
      from rfl,
    pullbackFiberOfFiberHom_fac, pullbackFiberOfHom_fac]

/-- The canonical morphism from the descent pair of the object that `A` attaches to an arrow of its
covering sieve, read on `CategoryTheory.Functor.DescentPair.ofObj` of the underlying object of
`𝒳`. -/
noncomputable def DescentPair.datumHomObj (A : DescentPair p J) {V : 𝒮} (g : V ⟶ A.pt)
    (hg : A.sieve.arrows g) : (toDescentPair p J).obj (A.datum.obj g hg).1 ⟶ A :=
  eqToHom (DescentPair.ofFiber_eq_ofObj (A.datum.obj g hg) J).symm ≫ A.datumHom g hg

/-- `CategoryTheory.Functor.DescentPair.datumHomObj A g hg` is cartesian over `g`. -/
theorem isCartesian_datumHomObj (A : DescentPair p J) {V : 𝒮} (g : V ⟶ A.pt)
    (hg : A.sieve.arrows g) : (p.descentPairProj J).IsCartesian g (A.datumHomObj g hg) := by
  exact isCartesian_iso_comp_of_isHomLift
    (eqToIso (DescentPair.ofFiber_eq_ofObj (A.datum.obj g hg) J).symm)
    (isHomLift_eqToHom_ofFiber J (A.datum.obj g hg)) (isCartesian_datumHom A g hg)

/-- **The canonical morphisms are compatible with the contractions of the datum**, in the spelling
that uses the 1-morphism `CategoryTheory.Functor.toDescentPair`. -/
theorem DescentPair.map_contract_comp_datumHomObj (A : DescentPair p J) {V W : 𝒮} {g : V ⟶ A.pt}
    (hg : A.sieve.arrows g) (γ : W ⟶ V) {b : W ⟶ A.pt} (hb : A.sieve.arrows b) (hγ : γ ≫ g = b) :
    (toDescentPair p J).map (Fiber.fiberInclusion.map (A.datum.contract hg γ hb hγ).hom) ≫
        A.datumHomObj b hb =
      (toDescentPair p J).map (IsPreFibered.pullbackMap (A.datum.obj g hg).2 γ) ≫
        A.datumHomObj g hg := by
  have h :=
    congrArg
      (fun t ↦
        eqToHom (DescentPair.ofFiber_eq_ofObj (pullbackFiber p (A.datum.obj g hg) γ) J).symm ≫ t)
      (A.ofFiberMor_contract_comp_datumHom hg γ hb hγ)
  simp only [← Category.assoc, eqToHom_comp_ofFiberMor] at h
  simpa only [DescentPair.datumHomObj, Category.assoc] using h

end SelfDescent

/-! ### Effective descent for the third stage

Let `D` be a descent datum for the third stage relative to a covering sieve `R` of `U`. Over the
glued sieve `CategoryTheory.Functor.SieveDescentDatum.glueSieve` each of its objects is, by
clause (2) of Stacks 02ZN, the image of an object of the source; so the restriction of `D` to that
sieve descends (`CategoryTheory.Functor.SieveDescentDatum.descendAlong`) to a descent datum *in
the source*, and the descent pair it forms is the object the restriction of `D` descends to
(`CategoryTheory.Functor.DescentPair.map_contract_comp_datumHomObj`). Effectiveness of `D` itself
then follows because effectiveness is local on the base
(`CategoryTheory.Functor.SieveDescentDatum.isEffective_of_restrict`). -/

section Effective

universe w t₁ t₂
variable {𝒞 : Type t₁} [Category.{vb} 𝒞] {𝒴 : Type t₂} [Category.{max t₁ t₂ w vb} 𝒴]
  {q : 𝒴 ⥤ 𝒞} [q.IsFibered] {J : GrothendieckTopology 𝒞} {U : 𝒞} {R : Sieve U}

/-- The pair that a descent datum of descent pairs attaches to an arrow of its sieve, normalised,
is isomorphic in the fibre to the pair the datum attaches to that arrow. -/
noncomputable def SieveDescentDatum.pairFiberAtIso (D : SieveDescentDatum (q.descentPairProj J) R)
    {V : 𝒞} (f : V ⟶ U) (hf : R.arrows f) :
    Fiber.mk (show (q.descentPairProj J).obj (D.pairAt f hf) = V from rfl) ≅ D.obj f hf :=
  have hid :
    (q.descentPairProj J).IsHomLift (eqToHom (show V = (D.obj f hf).1.pt from (D.obj f hf).2.symm))
      (𝟙 (D.obj f hf).1) :=
    IsHomLift.of_fac' _ _ _ (D.obj f hf).2 rfl (by simp)
  have := hid
  have hcart :
    (q.descentPairProj J).IsCartesian
      (eqToHom (show V = (D.obj f hf).1.pt from (D.obj f hf).2.symm)) (𝟙 (D.obj f hf).1) :=
    inferInstance
  have hpb :=
    isStronglyCartesian_pullbackHom (D.obj f hf).1
      (eqToHom (show V = (D.obj f hf).1.pt from (D.obj f hf).2.symm))
  have := hpb
  fiberIsoOfCartesian (eqToHom (show V = (D.obj f hf).1.pt from (D.obj f hf).2.symm))
    (DescentMor.mk
      (DescentPairData.pullbackHom (D.obj f hf).1
        (eqToHom (show V = (D.obj f hf).1.pt from (D.obj f hf).2.symm))))
    (𝟙 (D.obj f hf).1) inferInstance hcart

/-- **The object of the source that the glued datum attaches to an arrow of the glued sieve is, in
the third stage, the object the given datum attaches to it.** This is clause (2) of Stacks 02ZN,
read at the chosen factorisation of the arrow. -/
noncomputable def SieveDescentDatum.glueObjIso (D : SieveDescentDatum (q.descentPairProj J) R)
    {W : 𝒞} {h : W ⟶ U} (hh : D.glueSieve.arrows h) (hR : R.arrows h) :
    (fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq W).obj (D.glueObj hh) ≅
      D.obj h hR :=
  have hcart :=
    isCartesian_datumHomObj (D.pairAt (D.factor hh).arr (D.factor hh).mem) (D.factor hh).loc
      (D.factor hh).loc_mem
  have := hcart
  fiberIsoOfCartesian (D.factor hh).loc
      ((D.pairAt (D.factor hh).arr (D.factor hh).mem).datumHomObj (D.factor hh).loc
        (D.factor hh).loc_mem)
      (IsPreFibered.pullbackMap
        (Fiber.mk
            (show (q.descentPairProj J).obj (D.pairAt (D.factor hh).arr (D.factor hh).mem) = _ from
              rfl)).2
        (D.factor hh).loc)
      inferInstance (IsPreFibered.pullbackMap.IsCartesian _ _) ≪≫
    pullbackFiberIso (D.pairFiberAtIso (D.factor hh).arr (D.factor hh).mem) (D.factor hh).loc ≪≫
    D.contract (D.factor hh).mem (D.factor hh).loc hR (D.factor hh).fac

/-- The glued sieve refines the sieve the datum is relative to. -/
theorem SieveDescentDatum.glueSieve_le (D : SieveDescentDatum (q.descentPairProj J) R) :
    D.glueSieve ≤ R := by
  rintro W h ⟨V, f, hf, g, -, rfl⟩
  exact R.downward_closed hf g

/-- **The descent datum in the source that a descent datum of descent pairs glues to.** Its objects
are the objects `CategoryTheory.Functor.SieveDescentDatum.glueObj`, and its gluing isomorphisms
are the unique preimages, under the 1-morphism into the third stage, of the gluing isomorphisms of
the given datum. -/
noncomputable def SieveDescentDatum.glueDatum
    (hmor : ∀ (V : 𝒞) (x y : q.Fiber V), IsMorSheaf q J V x y)
    (hsep : ∀ {x y : 𝒴} {a b : x ⟶ y}, q.LocallyEqual J a b → a = b)
    (D : SieveDescentDatum (q.descentPairProj J) R) : SieveDescentDatum q D.glueSieve :=
  (D.restrict D.glueSieve_le).descendAlong (isFibrewiseFullyFaithful_toDescentPair hmor hsep)
    (fun _ _ hh ↦ D.glueObj hh) (fun _ h hh ↦ D.glueObjIso hh (D.glueSieve_le h hh))

/-- **The descent pair that a descent datum of descent pairs amalgamates to.** -/
noncomputable def SieveDescentDatum.gluePair
    (hmor : ∀ (V : 𝒞) (x y : q.Fiber V), IsMorSheaf q J V x y)
    (hsep : ∀ {x y : 𝒴} {a b : x ⟶ y}, q.LocallyEqual J a b → a = b)
    (D : SieveDescentDatum (q.descentPairProj J) R) (hR : R ∈ J U) : DescentPair q J
    where
  pt := U
  sieve := D.glueSieve
  sieve_mem := D.glueSieve_mem hR
  datum := D.glueDatum hmor hsep

/-- The contraction of the glued datum, read through the 1-morphism into the third stage. -/
theorem SieveDescentDatum.map_glueDatum_contract
    (hmor : ∀ (V : 𝒞) (x y : q.Fiber V), IsMorSheaf q J V x y)
    (hsep : ∀ {x y : 𝒴} {a b : x ⟶ y}, q.LocallyEqual J a b → a = b)
    (D : SieveDescentDatum (q.descentPairProj J) R) {V W : 𝒞} {h : V ⟶ U}
    (hh : D.glueSieve.arrows h) (γ : W ⟶ V) {b : W ⟶ U} (hb' : D.glueSieve.arrows b)
    (hb : γ ≫ h = b) :
    (fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq W).map
        ((D.glueDatum hmor hsep).contract hh γ hb' hb).hom =
      ((isFibredOneMorphism_toDescentPair q J).mapPullbackFiberIso (D.glueObj hh) γ).inv ≫
        (((D.restrict D.glueSieve_le).toImage (isFibredOneMorphism_toDescentPair q J)
                (fun _ _ hh ↦ D.glueObj hh)
                (fun _ h hh ↦ D.glueObjIso hh (D.glueSieve_le h hh))).contract
            hh γ hb' hb).hom :=
  SieveDescentDatum.map_descendAlong_contract _ _ _ _ hh γ hb' hb

/-- **The restriction of a descent datum of descent pairs to the glued sieve descends to the
amalgamated pair.** -/
theorem SieveDescentDatum.isEffective_restrict_glueSieve
    (hmor : ∀ (V : 𝒞) (x y : q.Fiber V), IsMorSheaf q J V x y)
    (hsep : ∀ {x y : 𝒴} {a b : x ⟶ y}, q.LocallyEqual J a b → a = b)
    (D : SieveDescentDatum (q.descentPairProj J) R) (hR : R ∈ J U) :
    (D.restrict D.glueSieve_le).IsEffective := by
  have hζcart :
    ∀ ⦃W : 𝒞⦄ (h : W ⟶ U) (hh : D.glueSieve.arrows h),
      (q.descentPairProj J).IsCartesian h
        (Fiber.fiberInclusion.map (D.glueObjIso hh (D.glueSieve_le h hh)).inv ≫
          (D.gluePair hmor hsep hR).datumHomObj h hh) := by
    intro W h hh
    exact isCartesian_iso_comp_of_isHomLift
      (Fiber.fiberInclusion.mapIso (D.glueObjIso hh (D.glueSieve_le h hh))).symm
      (D.glueObjIso hh (D.glueSieve_le h hh)).inv.2
      (isCartesian_datumHomObj (D.gluePair hmor hsep hR) h hh)
  refine
    ⟨Fiber.mk (show (q.descentPairProj J).obj (D.gluePair hmor hsep hR) = U from rfl),
      fun {_W} h hh ↦
      Fiber.fiberInclusion.map (D.glueObjIso hh (D.glueSieve_le h hh)).inv ≫
        (D.gluePair hmor hsep hR).datumHomObj h hh,
      (D.restrict D.glueSieve_le).descends_of_isoAlong _ _ hζcart ?_⟩
  intro V W h hh γ b hb hb'
  have h1 :
    ((D.restrict D.glueSieve_le).contract hh γ hb' hb).hom ≫
        (D.glueObjIso hb' (D.glueSieve_le b hb')).inv =
      pullbackFiberHom (D.glueObjIso hh (D.glueSieve_le h hh)).inv γ ≫
        (((D.restrict D.glueSieve_le).toImage (isFibredOneMorphism_toDescentPair q J)
                (fun _ _ hh ↦ D.glueObj hh)
                (fun _ h hh ↦ D.glueObjIso hh (D.glueSieve_le h hh))).contract
            hh γ hb' hb).hom := by
    rw [SieveDescentDatum.toImage_contract, ← Category.assoc, pullbackFiberHom_inv_hom_id,
      Category.id_comp]
  have h2 :
    (((D.restrict D.glueSieve_le).toImage (isFibredOneMorphism_toDescentPair q J)
              (fun _ _ hh ↦ D.glueObj hh)
              (fun _ h hh ↦ D.glueObjIso hh (D.glueSieve_le h hh))).contract
          hh γ hb' hb).hom =
      ((isFibredOneMorphism_toDescentPair q J).mapPullbackFiberIso (D.glueObj hh) γ).hom ≫
        (fiberFunctorOfCompEq (isFibredOneMorphism_toDescentPair q J).comp_eq W).map
          ((D.glueDatum hmor hsep).contract hh γ hb' hb).hom := by
    rw [D.map_glueDatum_contract hmor hsep hh γ hb' hb, Iso.hom_inv_id_assoc]
  have hstar :
    (q.toDescentPair J).map
          (Fiber.fiberInclusion.map ((D.glueDatum hmor hsep).contract hh γ hb' hb).hom) ≫
        (D.gluePair hmor hsep hR).datumHomObj b hb' =
      (q.toDescentPair J).map (IsPreFibered.pullbackMap (D.glueObj hh).2 γ) ≫
        (D.gluePair hmor hsep hR).datumHomObj h hh :=
    (D.gluePair hmor hsep hR).map_contract_comp_datumHomObj hh γ hb' hb
  rw [← Category.assoc, ← Functor.map_comp, h1, h2, Functor.map_comp, Functor.map_comp,
    fiberInclusion_map_fiberFunctorOfCompEq_map]
  simp only [Category.assoc]
  rw [hstar, IsFibredOneMorphism.mapPullbackFiberIso_hom_fac_assoc, pullbackFiberHom_fac_assoc]

/-- **Every descent datum for the third stage is effective**, as soon as the morphism presheaves of
the source are sheaves and its locally equal morphisms are equal. -/
theorem hasEffectiveDescent_descentPairProj
    (hmor : ∀ (V : 𝒞) (x y : q.Fiber V), IsMorSheaf q J V x y)
    (hsep : ∀ {x y : 𝒴} {a b : x ⟶ y}, q.LocallyEqual J a b → a = b) :
    HasEffectiveDescent (q.descentPairProj J) J := by
  intro U R hR D
  exact
    D.isEffective_of_restrict (isMorSheaf_descentPairProj hmor hsep) D.glueSieve_le
      (D.glueSieve_mem hR) (D.isEffective_restrict_glueSieve hmor hsep hR)

/-! ### The third stage of the stackification is a stack -/

/-- **Every descent datum for the third stage of the construction of the stackification is
effective**: condition (3) of Stacks 026F for
`CategoryTheory.Functor.stageThreeProj`. The two hypotheses of
`CategoryTheory.Functor.hasEffectiveDescent_descentPairProj` are supplied by the first two stages,
`CategoryTheory.Functor.isMorSheaf_stageTwoProj` and
`CategoryTheory.Functor.locallyEqual_stageTwoProj_iff`. -/
theorem hasEffectiveDescent_stageThreeProj (q : 𝒴 ⥤ 𝒞) [q.IsFibered] (J : GrothendieckTopology 𝒞) :
    HasEffectiveDescent (q.stageThreeProj J) J :=
  hasEffectiveDescent_descentPairProj (isMorSheaf_stageTwoProj q J)
    (fun hab ↦ (locallyEqual_stageTwoProj_iff _ _).mp hab)

/-- **The third stage of the construction of the stackification of a fibred category is a
stack.** -/
theorem isStack_stageThreeProj (q : 𝒴 ⥤ 𝒞) [q.IsFibered] (J : GrothendieckTopology 𝒞) :
    IsStack (q.stageThreeProj J) J
    where
  isFibered := isFibered_stageThreeProj q J
  isMorSheaf := isMorSheaf_stageThreeProj q J
  hasEffectiveDescent := hasEffectiveDescent_stageThreeProj q J

end Effective

end CategoryTheory.Functor
