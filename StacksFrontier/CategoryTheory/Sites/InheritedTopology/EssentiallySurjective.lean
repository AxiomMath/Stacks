module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.DescentUniqueness
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibreFunctor

/-!
# Local essential surjectivity of a fully faithful 1-morphism into a stack

Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be fibred categories over `𝒞` and let
`F : 𝒳 ⥤ 𝒴` be a fully faithful 1-morphism of fibred categories over `𝒞`. Suppose an object `x`
of the fibre of `𝒴` over `U` becomes, along the members of a covering sieve `R` of `U`,
isomorphic to an object in the image of `F`. This file shows that if `p` is a stack and the
presheaves `Mor` of `q` are sheaves, then `x` is *globally* in the image of `F` on the fibre over
`U`.

## Main definitions

* `CategoryTheory.Functor.LocalPreimage.descentDatum`: the descent datum for `𝒳` relative to `R`
  built from local preimages `z f` and isomorphisms `φ f : F (z f) ≅ f^* x`.

## Main results

* `CategoryTheory.Functor.LocalPreimage.glueIso_fac`: the characterization of the gluing
  isomorphisms of that descent datum.
* `CategoryTheory.Functor.LocalPreimage.nonempty_iso_of_descends`: an object descending the
  datum has an `F`-image isomorphic to `x`.
* `CategoryTheory.Functor.exists_iso_of_locally_essImage`: an object locally in the image of a
  fully faithful 1-morphism into a stack is in its image.

## Implementation notes

The fibre inclusion, the induced functor on fibres and the chosen pullbacks are semireducible,
so several identities between composites hold only once these unfold; their proofs are elaborated
with `backward.isDefEq.respectTransparency` disabled.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe vb v v₁ v₂ v₃ u₁ u₂ u₃

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

/-! ### Cocycle and base-change identities for the canonical comparisons of one object -/

section Comparison

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
  {q : 𝒴 ⥤ 𝒞} [q.IsFibered] {U : 𝒞}

/-- The canonical comparisons of the chosen pullbacks of one object compose. -/
lemma pullbackFiberComparison_comp (x : q.Fiber U) {V W X' Z : 𝒞} {f : V ⟶ U} {g : W ⟶ U}
    {h : X' ⟶ U} (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (ε₃ : Z ⟶ X') (h₁₂ : ε₁ ≫ f = ε₂ ≫ g)
    (h₂₃ : ε₂ ≫ g = ε₃ ≫ h) (h₁₃ : ε₁ ≫ f = ε₃ ≫ h) :
    (pullbackFiberComparison x ε₁ ε₂ h₁₂).hom ≫ (pullbackFiberComparison x ε₂ ε₃ h₂₃).hom =
      (pullbackFiberComparison x ε₁ ε₃ h₁₃).hom :=
  (SieveDescentDatum.ofFiber x ⊤).cocycle (f := f) trivial (g := g) trivial (h := h) trivial
    ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃

/-- The canonical comparisons of the chosen pullbacks of one object are compatible with base
change. -/
lemma pullbackFiberComparison_pullback (x : q.Fiber U) {V W Z Z' : 𝒞} {f : V ⟶ U} {g : W ⟶ U}
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z) :
    (pullbackFiberCompIso (pullbackFiber q x f) ε γ).inv ≫
        (pullbackFiberIso (pullbackFiberComparison x ε ε' heq) γ).hom ≫
        (pullbackFiberCompIso (pullbackFiber q x g) ε' γ).hom =
      (pullbackFiberComparison x (γ ≫ ε) (γ ≫ ε')
        (by rw [Category.assoc, Category.assoc, heq])).hom :=
  (SieveDescentDatum.ofFiber x ⊤).iso_pullback (f := f) trivial (g := g) trivial ε ε' heq γ

/-- The descent datum of an object descends to that object, along its chosen cartesian lifts. -/
lemma ofFiber_descends (x : q.Fiber U) (R : Sieve U) :
    (SieveDescentDatum.ofFiber x R).Descends q x
      (fun {_V} f _ => IsPreFibered.pullbackMap x.2 f) :=
  ⟨fun {_V} f _ => IsPreFibered.pullbackMap.IsCartesian x.2 f,
    fun {_V _W _Z} {_f} _ {_g} _ ε ε' heq => pullbackFiberComparison_hom_fac x ε ε' heq⟩

end Comparison

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-! ### The descent datum of a family of local preimages -/

namespace LocalPreimage

variable {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} [p.IsFibered] [q.IsFibered] {F : 𝒳 ⥤ 𝒴}
variable (hF : IsFibredOneMorphism p q F)
variable {U : 𝒞} {x : q.Fiber U} {R : Sieve U}
variable (z : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → p.Fiber V)
variable (φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
  (Fiber.mapOfComp p q F hF.comp_eq V).obj (z f hf) ≅ pullbackFiber q x f)

/-- The cartesian morphism `F (ε^* (z f)) ⟶ x` over `ε ≫ f` that the local data provide: the
`F`-image of the chosen cartesian lift of `ε`, followed by the local isomorphism at `f` and the
chosen cartesian lift of `f`. -/
noncomputable def localMor ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (ε : W ⟶ V) :
    ((Fiber.mapOfComp p q F hF.comp_eq W).obj (pullbackFiber p (z f hf) ε)).1 ⟶ x.1 :=
  F.map (IsPreFibered.pullbackMap (z f hf).2 ε) ≫
    Fiber.fiberInclusion.map (φ f hf).hom ≫ IsPreFibered.pullbackMap x.2 f

/-- Precomposing a strongly cartesian morphism with an isomorphism of the fibre keeps it strongly
cartesian over the same base morphism. -/
private lemma isStronglyCartesian_fiberInclusion_map_comp {q : 𝒴 ⥤ 𝒞} {V U : 𝒞}
    {a b : q.Fiber V} (e : a ≅ b) {Y : 𝒴} (f : V ⟶ U) (g : b.1 ⟶ Y)
    [q.IsStronglyCartesian f g] : q.IsStronglyCartesian f (Fiber.fiberInclusion.map e.hom ≫ g) := by
  have h : q.IsStronglyCartesian (𝟙 V) (Fiber.fiberInclusion.map e.hom) :=
    have : q.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map e.hom) := e.hom.2
    IsStronglyCartesian.of_isIso q (𝟙 V) _
  simpa using (inferInstance : q.IsStronglyCartesian (𝟙 V ≫ f) _)

set_option backward.isDefEq.respectTransparency false in
/-- `CategoryTheory.Functor.LocalPreimage.localMor` is strongly cartesian over `ε ≫ f`. -/
lemma localMor_isStronglyCartesian ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (ε : W ⟶ V) :
    q.IsStronglyCartesian (ε ≫ f) (localMor hF z φ f hf ε) := by
  have := hF.map_isStronglyCartesian ε (IsPreFibered.pullbackMap (z f hf).2 ε) inferInstance
  have := isStronglyCartesian_fiberInclusion_map_comp (φ f hf) f (IsPreFibered.pullbackMap x.2 f)
  rw [localMor]
  infer_instance

/-- The weak form of `CategoryTheory.Functor.LocalPreimage.localMor_isStronglyCartesian`:
`CategoryTheory.Functor.LocalPreimage.localMor` is cartesian over `ε ≫ f`. -/
lemma localMor_isCartesian ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (ε : W ⟶ V) :
    q.IsCartesian (ε ≫ f) (localMor hF z φ f hf ε) :=
  have := localMor_isStronglyCartesian hF z φ f hf ε
  inferInstance

/-- The comparison, in the fibre of `𝒴` over `Z`, of the two cartesian morphisms to `x` over one
and the same base morphism that the local data provide at a pair of members of the sieve. -/
noncomputable def localIso ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (Fiber.mapOfComp p q F hF.comp_eq Z).obj (pullbackFiber p (z f hf) ε) ≅
      (Fiber.mapOfComp p q F hF.comp_eq Z).obj (pullbackFiber p (z g hg) ε') :=
  fiberIsoOfCartesian (ε ≫ f) (localMor hF z φ f hf ε) (localMor hF z φ g hg ε')
    (localMor_isCartesian hF z φ f hf ε)
    (heq ▸ localMor_isCartesian hF z φ g hg ε')

/-- The defining property of `CategoryTheory.Functor.LocalPreimage.localIso`: composing it with
the cartesian morphism of the local data at `(g, ε')` gives the one at `(f, ε)`. -/
@[reassoc]
lemma localIso_hom_fac ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    Fiber.fiberInclusion.map (localIso hF z φ hf hg ε ε' heq).hom ≫
        localMor hF z φ g hg ε' = localMor hF z φ f hf ε :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The cartesian morphism of the local data at `(f, γ ≫ ε)` is the one at `(f, ε)`, precomposed
with the contraction of the iterated chosen pullback and the chosen cartesian lift of `γ`. -/
lemma localMor_comp_base ⦃V W W' : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (ε : W ⟶ V) (γ : W' ⟶ W) :
    F.map (Fiber.fiberInclusion.map (pullbackFiberCompIso (z f hf) ε γ).inv) ≫
        F.map (IsPreFibered.pullbackMap (pullbackFiber p (z f hf) ε).2 γ) ≫
        localMor hF z φ f hf ε =
      localMor hF z φ f hf (γ ≫ ε) := by
  rw [localMor, localMor, ← Category.assoc (F.map _) (F.map _), ← F.map_comp,
    ← Category.assoc, ← F.map_comp, Category.assoc, pullbackFiberCompIso_inv_fac]

set_option backward.isDefEq.respectTransparency false in
/-- The dual form of `CategoryTheory.Functor.LocalPreimage.localMor_comp_base`, with the
contraction of the iterated chosen pullback on the other side. -/
lemma localMor_comp_base' ⦃V W W' : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (ε : W ⟶ V) (γ : W' ⟶ W) :
    F.map (Fiber.fiberInclusion.map (pullbackFiberCompIso (z f hf) ε γ).hom) ≫
        localMor hF z φ f hf (γ ≫ ε) =
      F.map (IsPreFibered.pullbackMap (pullbackFiber p (z f hf) ε).2 γ) ≫
        localMor hF z φ f hf ε := by
  rw [localMor, localMor, ← Category.assoc (F.map _) (F.map _), ← F.map_comp,
    ← Category.assoc (F.map _) (F.map _), ← F.map_comp, pullbackFiberCompIso_hom_fac]

/-! ### The image of a descended object -/

/-- The comparison, in the fibre of `𝒴` over `W`, between the `F`-image of the chosen pullback of
a local preimage and the corresponding iterated chosen pullback of `x`. -/
noncomputable def imageIso ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (ε : W ⟶ V) :
    (Fiber.mapOfComp p q F hF.comp_eq W).obj (pullbackFiber p (z f hf) ε) ≅
      pullbackFiber q (pullbackFiber q x f) ε :=
  (mapPullbackFiberIso' hF (z f hf) ε).symm ≪≫ pullbackFiberIso (φ f hf) ε

set_option backward.isDefEq.respectTransparency false in
/-- The comparison `CategoryTheory.Functor.LocalPreimage.imageIso` carries the composite of the
two chosen cartesian lifts to the cartesian morphism of the local data. -/
@[reassoc]
lemma imageIso_hom_fac ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (ε : W ⟶ V) :
    Fiber.fiberInclusion.map (imageIso hF z φ f hf ε).hom ≫
        IsPreFibered.pullbackMap (pullbackFiber q x f).2 ε ≫
        IsPreFibered.pullbackMap x.2 f =
      localMor hF z φ f hf ε := by
  rw [imageIso, localMor]
  simp [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp, Category.assoc,
    pullbackFiberHom_fac_assoc, mapPullbackFiberIso'_inv_fac_assoc]

/-- The comparisons `CategoryTheory.Functor.LocalPreimage.imageIso` intertwine the gluing
isomorphisms of the local data with the canonical comparisons of the chosen pullbacks of `x`. -/
lemma localIso_imageIso ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (localIso hF z φ hf hg ε ε' heq).hom ≫ (imageIso hF z φ g hg ε').hom =
      (imageIso hF z φ f hf ε).hom ≫ (pullbackFiberComparison x ε ε' heq).hom := by
  have hcart : q.IsCartesian (ε ≫ f)
      (IsPreFibered.pullbackMap (pullbackFiber q x g).2 ε' ≫ IsPreFibered.pullbackMap x.2 g) := by
    have h0 := isCartesian_pullbackMap_comp_pullbackMap x g ε' (ε' ≫ g) rfl
    rwa [← heq] at h0
  refine fiber_hom_ext_of_cartesian (ε ≫ f) _ hcart _ _ ?_
  simp [Functor.map_comp, Category.assoc, imageIso_hom_fac,
    localIso_hom_fac, pullbackFiberComparison_hom_fac]

section FullyFaithful

variable [F.Full] [F.Faithful]

/-- The functor induced on the fibre over `V` by `F` is fully faithful. -/
noncomputable def fibreFullyFaithful (V : 𝒞) :
    (Fiber.mapOfComp p q F hF.comp_eq V).FullyFaithful :=
  have := Fiber.full_mapOfComp hF.comp_eq V
  have := Fiber.faithful_mapOfComp hF.comp_eq V
  Functor.FullyFaithful.ofFullyFaithful _

/-- Two morphisms of the fibre of `𝒳` over `Z` between chosen pullbacks of local preimages agree
as soon as their `F`-images do after composition with the cartesian morphism
`CategoryTheory.Functor.LocalPreimage.localMor` at the target. -/
lemma fibre_hom_ext ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (w w' : pullbackFiber p (z f hf) ε ⟶ pullbackFiber p (z g hg) ε')
    (h : F.map (Fiber.fiberInclusion.map w) ≫ localMor hF z φ g hg ε' =
      F.map (Fiber.fiberInclusion.map w') ≫ localMor hF z φ g hg ε') : w = w' := by
  refine (fibreFullyFaithful hF Z).map_injective ?_
  exact fiber_hom_ext_of_cartesian (ε' ≫ g) (localMor hF z φ g hg ε')
    (localMor_isCartesian hF z φ g hg ε') _ _ h

/-- The gluing isomorphism of the descent datum of the local preimages: the `F`-preimage of the
comparison `CategoryTheory.Functor.LocalPreimage.localIso`. -/
noncomputable def glueIso ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    pullbackFiber p (z f hf) ε ≅ pullbackFiber p (z g hg) ε' :=
  (fibreFullyFaithful hF Z).preimageIso (localIso hF z φ hf hg ε ε' heq)

/-- The `F`-image of the gluing isomorphism `CategoryTheory.Functor.LocalPreimage.glueIso` is the
comparison `CategoryTheory.Functor.LocalPreimage.localIso`. -/
lemma map_glueIso_hom ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    F.map (Fiber.fiberInclusion.map (glueIso hF z φ hf hg ε ε' heq).hom) =
      Fiber.fiberInclusion.map (localIso hF z φ hf hg ε ε' heq).hom :=
  congrArg Fiber.fiberInclusion.map
    ((fibreFullyFaithful hF Z).map_preimage (localIso hF z φ hf hg ε ε' heq).hom)

/-- The defining factorization of the gluing isomorphism: its `F`-image carries the cartesian
morphism of the local data at `(g, ε')` to the one at `(f, ε)`. -/
@[reassoc]
lemma glueIso_fac ⦃V W Z : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) {g : W ⟶ U}
    (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    F.map (Fiber.fiberInclusion.map (glueIso hF z φ hf hg ε ε' heq).hom) ≫
        localMor hF z φ g hg ε' = localMor hF z φ f hf ε := by
  rw [map_glueIso_hom hF z φ hf hg ε ε' heq]
  exact localIso_hom_fac hF z φ hf hg ε ε' heq

set_option backward.isDefEq.respectTransparency false in
/-- The descent datum for `𝒳` relative to `R` assembled from the local preimages: its object at
a member `f` of `R` is `z f`, and its gluing isomorphisms are
`CategoryTheory.Functor.LocalPreimage.glueIso`. -/
noncomputable def descentDatum : SieveDescentDatum p R where
  obj := fun {_V} f hf => z f hf
  iso := fun {_V _W _Z} {_f} hf {_g} hg ε ε' heq => glueIso hF z φ hf hg ε ε' heq
  cocycle := by
    intro V W X' Z f hf g hg h hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃
    refine fibre_hom_ext hF z φ hf hh ε₁ ε₃ _ _ ?_
    rw [Functor.map_comp, F.map_comp, Category.assoc,
      glueIso_fac hF z φ hg hh ε₂ ε₃ h₂₃, glueIso_fac hF z φ hf hg ε₁ ε₂ h₁₂,
      glueIso_fac hF z φ hf hh ε₁ ε₃ h₁₃]
  iso_pullback := by
    intro V W Z Z' f hf g hg ε ε' heq γ
    refine fibre_hom_ext hF z φ hf hg (γ ≫ ε) (γ ≫ ε') _ _ ?_
    have hswap : F.map (Fiber.fiberInclusion.map
          (pullbackFiberHom (glueIso hF z φ hf hg ε ε' heq).hom γ)) ≫
        F.map (IsPreFibered.pullbackMap (pullbackFiber p (z g hg) ε').2 γ) ≫
          localMor hF z φ g hg ε' =
      F.map (IsPreFibered.pullbackMap (pullbackFiber p (z f hf) ε).2 γ) ≫
        F.map (Fiber.fiberInclusion.map (glueIso hF z φ hf hg ε ε' heq).hom) ≫
          localMor hF z φ g hg ε' := by
      rw [← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp, pullbackFiberHom_fac]
    rw [glueIso_fac hF z φ hf hg (γ ≫ ε) (γ ≫ ε') (by rw [Category.assoc, Category.assoc, heq])]
    simp only [Functor.map_comp, Category.assoc, pullbackFiberIso_hom]
    rw [localMor_comp_base' hF z φ g hg ε' γ, hswap,
      glueIso_fac hF z φ hf hg ε ε' heq, localMor_comp_base hF z φ f hf ε γ]

/-- The `F`-image of an object of the fibre over `U` that the descent datum of the local
preimages descends to carries, over each member of the sieve, a cartesian morphism from the
chosen pullback of `x`. -/
noncomputable def imageDescendsMor {x₁ : p.Fiber U}
    (ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f), ((descentDatum hF z φ).obj f hf).1 ⟶ x₁.1)
    ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) :
    ((SieveDescentDatum.ofFiber x R).obj f hf).1 ⟶
      ((Fiber.mapOfComp p q F hF.comp_eq U).obj x₁).1 :=
  Fiber.fiberInclusion.map (φ f hf).inv ≫ F.map (ζ f hf)

set_option backward.isDefEq.respectTransparency false in
/-- The chosen cartesian lift of `ε` at `x^*f`, followed by
`CategoryTheory.Functor.LocalPreimage.imageDescendsMor`, is the `F`-image of the corresponding
composite in `𝒳`, after the comparison `CategoryTheory.Functor.LocalPreimage.imageIso`. -/
lemma imageIso_hom_comp_imageDescendsMor {x₁ : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f), ((descentDatum hF z φ).obj f hf).1 ⟶ x₁.1}
    ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (ε : W ⟶ V) :
    Fiber.fiberInclusion.map (imageIso hF z φ f hf ε).hom ≫
        IsPreFibered.pullbackMap (pullbackFiber q x f).2 ε ≫
        imageDescendsMor hF z φ ζ f hf =
      F.map (IsPreFibered.pullbackMap (z f hf).2 ε ≫ ζ f hf) := by
  rw [imageIso, imageDescendsMor]
  simp only [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp, Category.assoc,
    pullbackFiberHom_fac_assoc]
  rw [← Category.assoc (Fiber.fiberInclusion.map (φ f hf).hom),
    ← Fiber.fiberInclusion.map_comp, Iso.hom_inv_id, Fiber.fiberInclusion.map_id,
    Category.id_comp, mapPullbackFiberIso'_inv_fac_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **The `F`-image of a descended object is isomorphic to `x`.** If the descent datum of the
local preimages descends to an object `x₁` of the fibre of `𝒳` over `U`, then the `F`-image of
`x₁` and `x` both descend the descent datum of `x` relative to `R`, hence are isomorphic when the
presheaves `Mor` of `q` are sheaves on `𝒞/U`. -/
theorem nonempty_iso_of_descends {J : GrothendieckTopology 𝒞}
    (hmor : ∀ (a b : q.Fiber U), IsMorSheaf q J U a b) (hR : R ∈ J U)
    {x₁ : p.Fiber U}
    {ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f), ((descentDatum hF z φ).obj f hf).1 ⟶ x₁.1}
    (hζ : (descentDatum hF z φ).Descends p x₁ ζ) :
    Nonempty ((Fiber.mapOfComp p q F hF.comp_eq U).obj x₁ ≅ x) := by
  refine SieveDescentDatum.nonempty_iso_of_descends hmor hR
    (D := SieveDescentDatum.ofFiber x R)
    (ζ := imageDescendsMor hF z φ ζ) (ξ := fun {_V} f _ => IsPreFibered.pullbackMap x.2 f)
    ⟨?_, ?_⟩ (ofFiber_descends x R)
  · intro V f hf
    have := hF.map_isStronglyCartesian f (ζ f hf) (have := hζ.1 f hf; inferInstance)
    have : q.IsStronglyCartesian f (imageDescendsMor hF z φ ζ f hf) :=
      isStronglyCartesian_fiberInclusion_map_comp (φ f hf).symm f (F.map (ζ f hf))
    infer_instance
  · intro V W Z f hf g hg ε ε' heq
    have key : Fiber.fiberInclusion.map (pullbackFiberComparison x ε ε' heq).hom ≫
          IsPreFibered.pullbackMap (pullbackFiber q x g).2 ε' ≫
          imageDescendsMor hF z φ ζ g hg =
        IsPreFibered.pullbackMap (pullbackFiber q x f).2 ε ≫
          imageDescendsMor hF z φ ζ f hf := by
      refine (cancel_epi (Fiber.fiberInclusion.map (imageIso hF z φ f hf ε).hom)).1 ?_
      rw [← Category.assoc, ← Fiber.fiberInclusion.map_comp,
        ← localIso_imageIso hF z φ hf hg ε ε' heq, Fiber.fiberInclusion.map_comp,
        Category.assoc, imageIso_hom_comp_imageDescendsMor hF z φ g hg ε',
        imageIso_hom_comp_imageDescendsMor hF z φ f hf ε,
        ← map_glueIso_hom hF z φ hf hg ε ε' heq, ← F.map_comp]
      exact congrArg F.map (hζ.2 hf hg ε ε' heq)
    exact key

end FullyFaithful

end LocalPreimage

/-! ### Local essential surjectivity implies essential surjectivity -/

section EssImage

variable {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} [p.IsFibered] [q.IsFibered] {F : 𝒳 ⥤ 𝒴}

/-- **An object locally in the image of a fully faithful 1-morphism is in its image.** Let `F` be
a fully faithful 1-morphism of fibred categories over `𝒞` whose source has effective descent and
whose target has `Mor`-sheaves. If an object `x` of the fibre of `𝒴` over `U` becomes isomorphic
to an object in the image of `F` along the members of a covering sieve of `U`, then it is
isomorphic to an object in the image of `F` on the fibre over `U` itself. -/
theorem exists_iso_of_locally_essImage {J : GrothendieckTopology 𝒞}
    (hF : IsFibredOneMorphism p q F) [F.Full] [F.Faithful]
    (hdesc : HasEffectiveDescent p J) {U : 𝒞}
    (hmor : ∀ (a b : q.Fiber U), IsMorSheaf q J U a b)
    (x : q.Fiber U) {R : Sieve U} (hR : R ∈ J U)
    (hRess : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → ∃ z : p.Fiber V,
      Nonempty ((Fiber.mapOfComp p q F hF.comp_eq V).obj z ≅ pullbackFiber q x f)) :
    ∃ x₁ : p.Fiber U, Nonempty ((Fiber.mapOfComp p q F hF.comp_eq U).obj x₁ ≅ x) := by
  choose z hz using hRess
  set φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
      (Fiber.mapOfComp p q F hF.comp_eq V).obj (z f hf) ≅ pullbackFiber q x f :=
    fun {_V} f hf => (hz f hf).some with hφ
  obtain ⟨x₁, ζ, hζ⟩ := hdesc R hR (LocalPreimage.descentDatum hF z φ)
  exact ⟨x₁, LocalPreimage.nonempty_iso_of_descends hF z φ hmor hR hζ⟩

end EssImage

end CategoryTheory.Functor
