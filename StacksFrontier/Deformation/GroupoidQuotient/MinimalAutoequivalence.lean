module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRestrictionImmersion
public import StacksFrontier.CategoryTheory.Grothendieck.FibreInclusionMap
public import StacksFrontier.Deformation.FormalObject.ProrepresentableMorphism
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Groupoid.Loops
public import StacksFrontier.Deformation.GroupoidQuotient.Minimality
public import StacksFrontier.Deformation.Predeformation.ProrepresentableEndomorphism
public import StacksFrontier.Deformation.TangentSpace.Derivations
public import StacksFrontier.Deformation.TangentSpace.FunctorMap

/-!
# Autoequivalences of the quotient of a minimal groupoid in functors

A morphism `(U, R, s, t, c) → (U', R', s', t', c')` of groupoids in functors induces a functor
`[U/R] → [U'/R']` of the quotient categories over the base, namely
`CategoryTheory.Grothendieck.map` of the transformation of evaluated groupoids
`Deformation.GroupoidInFunctors.evaluationNatTrans`, read in `Cat` along
`CategoryTheory.Grpd.forgetToCat`.

For a minimal smooth prorepresentable groupoid in functors on `𝒞_Λ`, an endomorphism whose
induced endofunctor of `[U/R]` is an equivalence is an isomorphism. The differential of
`U → [U/R]` commutes with the two differentials, and the canonical map `Der_Λ(k, k) → TU` is
fixed by the differential of the endomorphism, so minimality forces that differential to be
injective, hence bijective because `TU` is finite dimensional; the endomorphism of `U` is then
an isomorphism by Stacks 06KP. The evaluated groupoids inherit fullness and faithfulness from
the quotient, which makes the endomorphism of `R` bijective as well.

## Main definitions

* `Deformation.GroupoidInFunctors.quotientMap`: the induced functor of quotient categories.

## Main results

* `Deformation.GroupoidInFunctors.isIso_of_quotientMap_isEquivalence`: an endomorphism of the
  groupoid in functors whose induced endofunctor of the quotient is an equivalence is itself an
  isomorphism. This is the differential argument of **Stacks 06KQ**; the tag itself is carried
  by `Deformation.GroupoidInFunctors.exists_isIso_hom_of_isEquivalence_endo`, which combines it
  with the realisation of an arbitrary 1-morphism of quotients.
* `Deformation.GroupoidInFunctors.isIso_quotientMap_of_isEquivalence`: the induced endofunctor
  of the quotient is then an isomorphism of categories on the nose.

## Implementation notes

The morphism of the quotients is taken here in the form a morphism of groupoids in functors as
in Definition 06K3 gives it; the induced functor lies over `𝒞_Λ` on the nose, and so does the
functor induced by the inverse morphism, so an isomorphism of categories here is an isomorphism
of categories cofibered in groupoids. An **arbitrary** 1-morphism of the quotients over `𝒞_Λ`
is isomorphic to one of this form by
`Deformation.GroupoidInFunctors.exists_hom_of_morphismOver`, which is what turns the results
here into the tag; that is done in
`StacksFrontier.Deformation.GroupoidQuotient.MinimalEquivalence`.

`Deformation.GroupoidInFunctors.evaluationNatTrans` is the groupoid-valued transformation; the
Grothendieck construction asks for a `Cat`-valued one, and
`AlgebraicGeometry.Stack.evaluationGroupoidFunctor G ⋙ CategoryTheory.Grpd.forgetToCat` is
`Deformation.evaluationFunctor G` by definition, so whiskering supplies it.

Fullness and faithfulness of the evaluated groupoids are read off from the fibre inclusions of
the Grothendieck construction: the inclusion of the fibre over an object of the base is faithful
and commutes with the induced functors, and a morphism of the quotient whose image has identity
base component has identity base component itself.

The differential is made `k`-linear by transporting along a representable presentation, where
it becomes the map of derivations attached to an endomorphism of the representing object, by
Yoneda for `𝒞_Λ` (Stacks 06HD).

## References

* [Stacks Project, Tag 06KQ](https://stacks.math.columbia.edu/tag/06KQ)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory

universe u v w

namespace GroupoidInFunctors

/-- A transport between an object and itself on the left of a morphism is absorbed. -/
private theorem transport_self_comp {C : Type*} [Category* C] {X Y : C} (p : X = X)
    (m : X ⟶ Y) : eqToHom p ≫ m = m := by
  rw [eqToHom_refl, Category.id_comp]

/-- Transports between objects that agree, on either side of a morphism, are absorbed. -/
private theorem transport_absorb {C : Type*} [Category* C] {X Y : C} (p : X = X) (q : Y = Y)
    (m : X ⟶ Y) : eqToHom p ≫ m ≫ eqToHom q = m := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Three successive transports on the left of a morphism amount to a single transport. -/
private theorem transport_triple_comp {C : Type*} [Category* C] {X₁ X₂ X₃ X₄ Y : C}
    (p : X₁ = X₂) (q : X₂ = X₃) (r : X₃ = X₄) (s : X₁ = X₄) (m : X₄ ⟶ Y) :
    eqToHom p ≫ eqToHom q ≫ eqToHom r ≫ m = eqToHom s ≫ m := by
  subst p q r
  simp

/-- Two morphisms of an evaluated groupoid with the same value in the arrow functor agree, after
transport along the identifications of their sources and of their targets. The second transport
is taken in the direction the goals of `CategoryTheory.Functor.ext` present it, so that it is
determined by unification. -/
private theorem eq_transport_of_evaluationArrowEquiv_eq {C : Type u} [Category.{v} C]
    (H : GroupoidInFunctors.{u, v, w} C) (T : C)
    {x x' y y' : H.Evaluation T} (hx : x = x') (hy : y' = y)
    (a : x ⟶ y) (b : x' ⟶ y')
    (h : (H.evaluationArrowEquiv T x y a).1 = (H.evaluationArrowEquiv T x' y' b).1) :
    a = eqToHom hx ≫ b ≫ eqToHom hy := by
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (H.evaluationArrowEquiv T _ _).injective (Subtype.ext h)

/-- Evaluation of a composite of morphisms of groupoids in functors is the composite of the
evaluations. -/
public theorem Hom.evaluation_comp {C : Type u} [Category.{v} C]
    {G H K : GroupoidInFunctors.{u, v, w} C} (F₁ : Hom G H) (F₂ : Hom H K) (T : C) :
    Hom.evaluation (Hom.comp F₁ F₂) T = F₁.evaluation T ⋙ F₂.evaluation T := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun x y a => ?_
  refine eq_transport_of_evaluationArrowEquiv_eq K T _ _ _ _ ?_
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Hom.evaluation_map_arrow]
  rfl

/-- Evaluation of the identity morphism of a groupoid in functors is the identity functor. -/
public theorem Hom.evaluation_id {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) :
    Hom.evaluation (Hom.id G) T = Functor.id (G.Evaluation T) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun x y a => ?_
  refine eq_transport_of_evaluationArrowEquiv_eq G T _ _ _ _ ?_
  simp only [Hom.evaluation_map_arrow]
  rfl

/-- The functor of quotient categories induced by a morphism of groupoids in functors: the
Grothendieck construction applied to the induced transformation of evaluated groupoids, read in
`Cat`. -/
public noncomputable def quotientMap {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H) :
    Grothendieck (evaluationFunctor G) ⥤ Grothendieck (evaluationFunctor H) :=
  Grothendieck.map (Functor.whiskerRight (evaluationNatTrans F) Grpd.forgetToCat)

/-- The induced functor on quotients lies over the base category. -/
public theorem quotientMap_over {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H) :
    quotientMap F ⋙ Grothendieck.forget (evaluationFunctor H) =
      Grothendieck.forget (evaluationFunctor G) := rfl

/-- The induced functor on quotients sends an object `⟨T, x⟩` to `⟨T, F(x)⟩`, applying the
object map of `F` over `T`. -/
@[simp]
public theorem quotientMap_obj {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H)
    (X : Grothendieck (evaluationFunctor G)) :
    (quotientMap F).obj X = ⟨X.base, F.mapObjects.app X.base X.fiber⟩ := rfl

/-- The induced functor on quotients of a composite is the composite of the induced
functors. -/
public theorem quotientMap_comp {C : Type u} [Category.{v} C]
    {G H K : GroupoidInFunctors.{u, v, w} C} (F₁ : Hom G H) (F₂ : Hom H K) :
    quotientMap (Hom.comp F₁ F₂) = quotientMap F₁ ⋙ quotientMap F₂ := by
  have h : Functor.whiskerRight (evaluationNatTrans (Hom.comp F₁ F₂)) Grpd.forgetToCat =
      Functor.whiskerRight (evaluationNatTrans F₁) Grpd.forgetToCat ≫
        Functor.whiskerRight (evaluationNatTrans F₂) Grpd.forgetToCat :=
    NatTrans.ext (funext fun T =>
      congrArg Functor.toCatHom (Hom.evaluation_comp F₁ F₂ T))
  rw [quotientMap, h]
  exact Grothendieck.map_comp_eq _ _

/-- The induced functor on quotients of an identity is the identity functor. -/
public theorem quotientMap_id {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) :
    quotientMap (Hom.id G) = Functor.id (Grothendieck (evaluationFunctor G)) := by
  have h : Functor.whiskerRight (evaluationNatTrans (Hom.id G)) Grpd.forgetToCat =
      𝟙 (evaluationFunctor G) :=
    NatTrans.ext (funext fun T => congrArg Functor.toCatHom (Hom.evaluation_id G T))
  rw [quotientMap, h, Grothendieck.map_id_eq]

/-- The functor induced on quotients acts on the image of the fibre over an object of the base
through the evaluation of the morphism there. -/
public theorem quotientMap_map_ι {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H) (T : C)
    {x y : G.Evaluation T} (a : x ⟶ y) :
    (quotientMap F).map ((Grothendieck.ι (evaluationFunctor G) T).map a) =
      (Grothendieck.ι (evaluationFunctor H) T).map ((F.evaluation T).map a) :=
  (Functor.congr_hom (Grothendieck.ι_comp_map
      (Functor.whiskerRight (evaluationNatTrans F) Grpd.forgetToCat) T) a).trans
    (transport_absorb _ _ _)

/-- A morphism of groupoids in functors whose induced functor on quotients is faithful has
faithful evaluations. -/
public theorem Hom.evaluation_faithful {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H) (T : C)
    [(quotientMap F).Faithful] : (F.evaluation T).Faithful where
  map_injective {_ _} _ _ hab :=
    (Grothendieck.ι (evaluationFunctor G) T).map_injective
      ((quotientMap F).map_injective
        (by rw [quotientMap_map_ι, quotientMap_map_ι, hab]))

/-- A morphism of groupoids in functors whose induced functor on quotients is full has full
evaluations: a morphism of a fibre of the quotient has an identity base component, so it is the
image of a morphism of the evaluated groupoid. -/
public theorem Hom.evaluation_full {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H) (T : C)
    [(quotientMap F).Full] : (F.evaluation T).Full where
  map_surjective {x y} β := by
    obtain ⟨⟨hb, hf⟩, hh⟩ := (quotientMap F).map_surjective
      (X := (⟨T, x⟩ : Grothendieck (evaluationFunctor G)))
      (Y := (⟨T, y⟩ : Grothendieck (evaluationFunctor G)))
      ((Grothendieck.ι (evaluationFunctor H) T).map β)
    obtain rfl : hb = 𝟙 T := congrArg Grothendieck.Hom.base hh
    refine ⟨eqToHom (G.objects.map_id_apply T x).symm ≫ hf, ?_⟩
    refine (Grothendieck.ι (evaluationFunctor H) T).map_injective ?_
    rw [← quotientMap_map_ι]
    refine Eq.trans (congrArg (quotientMap F).map ?_) hh
    refine Grothendieck.ext _ _ rfl ?_
    exact (transport_triple_comp _ _ _ rfl hf).trans (transport_self_comp rfl hf)

/-- A morphism of groupoids in functors with full and faithful evaluation at an object of the
base, and bijective there on objects, is bijective there on arrows. -/
public theorem Hom.mapArrows_app_bijective {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H) (T : C)
    [(F.evaluation T).Full] [(F.evaluation T).Faithful]
    (hobj : Function.Bijective (F.mapObjects.app T)) :
    Function.Bijective (F.mapArrows.app T) := by
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · have hs : G.source.app T a = G.source.app T b :=
      hobj.1 (by rw [← F.map_source, ← F.map_source, hab])
    have ht : G.target.app T a = G.target.app T b :=
      hobj.1 (by rw [← F.map_target, ← F.map_target, hab])
    let x : G.Evaluation T := G.source.app T a
    let y : G.Evaluation T := G.target.app T a
    let αa : x ⟶ y := (G.evaluationArrowEquiv T x y).symm ⟨a, rfl, rfl⟩
    let αb : x ⟶ y := (G.evaluationArrowEquiv T x y).symm ⟨b, hs.symm, ht.symm⟩
    have hαa : (G.evaluationArrowEquiv T x y αa).1 = a :=
      G.evaluationArrowEquiv_symm_val T ⟨a, rfl, rfl⟩
    have hαb : (G.evaluationArrowEquiv T x y αb).1 = b :=
      G.evaluationArrowEquiv_symm_val T ⟨b, hs.symm, ht.symm⟩
    have hmap : (F.evaluation T).map αa = (F.evaluation T).map αb := by
      refine (H.evaluationArrowEquiv T _ _).injective (Subtype.ext ?_)
      rw [Hom.evaluation_map_arrow, Hom.evaluation_map_arrow, hαa, hαb, hab]
    rw [← hαa, ← hαb, (F.evaluation T).map_injective hmap]
  · obtain ⟨x, hx⟩ := hobj.2 (H.source.app T b)
    obtain ⟨y, hy⟩ := hobj.2 (H.target.app T b)
    obtain ⟨α, hα⟩ := (F.evaluation T).map_surjective
      ((H.evaluationArrowEquiv T ((F.evaluation T).obj x) ((F.evaluation T).obj y)).symm
        ⟨b, hx.symm, hy.symm⟩)
    refine ⟨(G.evaluationArrowEquiv T x y α).1, ?_⟩
    rw [← Hom.evaluation_map_arrow F T α, hα]
    exact H.evaluationArrowEquiv_symm_val T ⟨b, hx.symm, hy.symm⟩

/-- A morphism of groupoids in functors both of whose components are bijective at every object
of the base is an isomorphism. -/
public theorem isIso_of_bijective_components {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : G ⟶ H)
    (hobj : ∀ T, Function.Bijective ((Hom.mapObjects F).app T))
    (harr : ∀ T, Function.Bijective ((Hom.mapArrows F).app T)) :
    IsIso F := by
  let _ : IsIso (Hom.mapObjects F) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun T => (isIso_iff_bijective _).2 (hobj T)
  let _ : IsIso (Hom.mapArrows F) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun T => (isIso_iff_bijective _).2 (harr T)
  let e := asIso (Hom.mapObjects F)
  let r := asIso (Hom.mapArrows F)
  have heo : ∀ (T : C) (z : H.objects.obj T),
      (Hom.mapObjects F).app T (e.inv.app T z) = z :=
    fun T z => congrArg (fun m => m z) (e.inv_hom_id_app T)
  have hro : ∀ (T : C) (z : H.arrows.obj T),
      (Hom.mapArrows F).app T (r.inv.app T z) = z :=
    fun T z => congrArg (fun m => m z) (r.inv_hom_id_app T)
  let F' : Hom H G :=
    { mapObjects := e.inv
      mapArrows := r.inv
      map_source := fun T a => (hobj T).1 (by rw [← Hom.map_source F, hro, heo])
      map_target := fun T a => (hobj T).1 (by rw [← Hom.map_target F, hro, heo])
      map_id := fun T x => (harr T).1 (by rw [hro, Hom.map_id F, heo])
      map_comp := fun T a b h => (harr T).1 <| by
        rw [← Hom.map_comp F]
        exact (H.compose_congr T _ h (hro T a) (hro T b)).trans
          (hro T (H.compose T a b h)).symm }
  exact ⟨F', Hom.ext e.hom_inv_id r.hom_inv_id, Hom.ext e.inv_hom_id r.inv_hom_id⟩

/-- The functor on quotients induced by an isomorphism of groupoids in functors is an
isomorphism of categories. -/
public theorem isIso_quotientMap {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : G ⟶ H) [IsIso F] :
    IsIso (quotientMap F).toCatHom := by
  have key : ∀ {X Y : GroupoidInFunctors.{u, v, w} C} (a : X ⟶ Y) (b : Y ⟶ X), a ≫ b = 𝟙 X →
      quotientMap a ⋙ quotientMap b = Functor.id _ := fun a b h => by
    rw [← quotientMap_comp]
    exact (congrArg quotientMap h).trans (quotientMap_id _)
  exact ⟨(quotientMap (inv F)).toCatHom, congrArg Functor.toCatHom (key _ _ (IsIso.hom_inv_id F)),
    congrArg Functor.toCatHom (key _ _ (IsIso.inv_hom_id F))⟩

/-- When the induced functor on quotients is full, two points of the object functor whose
images have the same class in the fibre of the quotient already have the same class there: an
arrow between the images is the image of an arrow between the points. -/
public theorem classOf_quotientFiberObject_of_full {C : Type u} [Category.{v} C]
    {G : GroupoidInFunctors.{u, v, w} C} (f : G ⟶ G) (A : C) [(quotientMap f).Full]
    (x y : G.objects.obj A)
    (h : classOf (BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G)))
          (quotientProjection_cofibered G)
          (quotientFiberObject G A ((Hom.mapObjects f).app A x)) =
        classOf (BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G)))
          (quotientProjection_cofibered G)
          (quotientFiberObject G A ((Hom.mapObjects f).app A y))) :
    classOf (BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G)))
        (quotientProjection_cofibered G) (quotientFiberObject G A x) =
      classOf (BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G)))
        (quotientProjection_cofibered G) (quotientFiberObject G A y) := by
  let _ : (Hom.evaluation f A).Full := Hom.evaluation_full f A
  obtain ⟨i⟩ := (Quotient.exact ((classOf_eq_iff_quotient_mk_eq _
    (quotientProjection_cofibered G) _ _).1 h) :
      Nonempty (quotientFiberObject G A ((Hom.mapObjects f).app A x) ≅
        quotientFiberObject G A ((Hom.mapObjects f).app A y)))
  obtain ⟨r, hrs, hrt⟩ := arrowOfQuotientFiberHom G A i.hom
  obtain ⟨a, -⟩ := (Hom.evaluation f A).map_surjective
    ((G.evaluationArrowEquiv A ((Hom.evaluation f A).obj x)
      ((Hom.evaluation f A).obj y)).symm ⟨r, hrs, hrt⟩)
  exact classOf_eq_of_isIsomorphic _ (quotientProjection_cofibered G) _ _
    ⟨quotientFiberIsoOfArrow G A (G.evaluationArrowEquiv A x y a).1
      (G.evaluationArrowEquiv A x y a).2.1 (G.evaluationArrowEquiv A x y a).2.2⟩

end GroupoidInFunctors

end

/-! ### Autoequivalences of the quotient of a minimal groupoid in functors -/

section
open CategoryTheory

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace GroupoidInFunctors

/-- An endomorphism of the object functor of a prorepresentable groupoid in functors fixes
every point of `U(k[ε])` whose tangent vector comes from a derivation of the residue field:
the triangle formed by the two copies of `Der_Λ(k, k) → TU` commutes. -/
private theorem mapObjects_app_eq_of_mem_derivationRange
    (G : GroupoidInFunctors.{_, max v w, max v w}
      (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpro : IsProrepresentable G) (f : G ⟶ G)
    (x : G.objects.obj (artinianDualNumbers.{u, w, v} Λ k))
    (hx : classOf (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
        (categoryOfElements_projection_isCofibered G.objects)
        (objectFiber (artinianDualNumbers.{u, w, v} Λ k) x) ∈
      Set.range (derivationToTangentSpace (Functor.Elements.π G.objects)
        (objects_isPredeformationCategory_of_isProrepresentable G hpro))) :
    (Hom.mapObjects f).app (artinianDualNumbers.{u, w, v} Λ k) x = x := by
  obtain ⟨D, hD⟩ := hx
  refine classOf_objectFiber_injective G.objects _ ?_
  refine Eq.trans (congrArg _ (Subtype.ext rfl) :
    classOf (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
        (categoryOfElements_projection_isCofibered G.objects)
        (objectFiber (artinianDualNumbers.{u, w, v} Λ k)
          ((Hom.mapObjects f).app (artinianDualNumbers.{u, w, v} Λ k) x))
    = classOf (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
        (categoryOfElements_projection_isCofibered G.objects)
        ((fiberFunctor (elementsBasedFunctor (Hom.mapObjects f))
          (artinianDualNumbers.{u, w, v} Λ k)).obj
          (objectFiber (artinianDualNumbers.{u, w, v} Λ k) x))) ?_
  exact (mapIsomorphismClasses_classOf _ _ _ _).symm.trans <|
    (congrArg (mapIsomorphismClasses (categoryOfElements_projection_isCofibered G.objects)
      (categoryOfElements_projection_isCofibered G.objects)
      (elementsBasedFunctor (Hom.mapObjects f)) (artinianDualNumbers.{u, w, v} Λ k))
        hD.symm).trans <|
    (derivationToTangentSpace_naturality (Functor.Elements.π G.objects)
      (objects_isPredeformationCategory_of_isProrepresentable G hpro)
      (Functor.Elements.π G.objects)
      (objects_isPredeformationCategory_of_isProrepresentable G hpro)
      (elementsBasedFunctor (Hom.mapObjects f)) D).trans hD

variable (G : GroupoidInFunctors.{_, max v w, max v w}
  (ArtinianLocalAlgCat.{u, max v w, w} Λ k))

/-- The differential of an endomorphism of the object functor of a minimal smooth
prorepresentable groupoid in functors whose quotient endofunctor is full is bijective: it is
injective because the kernel of the differential of `U → [U/R]` lies in the image of
`Der_Λ(k, k)`, which the differential fixes, and then bijective because `TU` is
finite dimensional. -/
private theorem bijective_mapObjects_app_dualNumbers [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hpro : IsProrepresentable G) (hsmooth : IsSmooth G) (hmin : IsMinimal.{u, v, w, v} G)
    (f : G ⟶ G) [(quotientMap f).Full] :
    Function.Bijective
      ((Hom.mapObjects f).app (artinianDualNumbers.{u, w, v} Λ k)) := by
  classical
  obtain ⟨R, ⟨e⟩⟩ := ((isProrepresentable_iff_objects_arrows G).1 hpro).1
  have hei : ∀ x, e.inv.app (artinianDualNumbers.{u, w, v} Λ k)
      (e.hom.app (artinianDualNumbers.{u, w, v} Λ k) x) = x := fun x =>
    congrArg (fun m => m x) (e.hom_inv_id_app (artinianDualNumbers.{u, w, v} Λ k))
  have hinvbij := (isIso_iff_bijective (e.inv.app (artinianDualNumbers.{u, w, v} Λ k))).1
    inferInstance
  obtain ⟨g, hg⟩ := (restrictedCoyonedaMap_bijective R R).2 (e.inv ≫ Hom.mapObjects f ≫ e.hom)
  have hL : ∀ y, e.inv.app (artinianDualNumbers.{u, w, v} Λ k)
      (tangentSpaceMapArtinian.{u, v, w} g y) =
      (Hom.mapObjects f).app (artinianDualNumbers.{u, w, v} Λ k)
        (e.inv.app (artinianDualNumbers.{u, w, v} Λ k) y) := fun y => by
    have h1 : tangentSpaceMapArtinian.{u, v, w} g y =
        e.hom.app (artinianDualNumbers.{u, w, v} Λ k)
          ((Hom.mapObjects f).app (artinianDualNumbers.{u, w, v} Λ k)
            (e.inv.app (artinianDualNumbers.{u, w, v} Λ k) y)) := by
      rw [tangentSpaceMapArtinian_apply]
      exact congrArg (fun t => t.app (artinianDualNumbers.{u, w, v} Λ k) y) hg
    rw [h1, hei]
  have _ : FiniteDimensional k (tangentSpaceArtinian Λ k (restrictedCoyoneda R)) :=
    tangentSpace_finiteDimensional R
  obtain ⟨X₀, hX₀⟩ := classOf_surjective
    (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
    (categoryOfElements_projection_isCofibered G.objects) (artinianDualNumbers.{u, w, v} Λ k)
    (derivationToTangentSpace (Functor.Elements.π G.objects)
      (objects_isPredeformationCategory_of_isProrepresentable G hpro) 0)
  obtain ⟨u₀, rfl⟩ := objectFiber_surjective (artinianDualNumbers.{u, w, v} Λ k) X₀
  have hu₀ : (Hom.mapObjects f).app (artinianDualNumbers.{u, w, v} Λ k) u₀ = u₀ :=
    mapObjects_app_eq_of_mem_derivationRange G hpro f u₀ ⟨0, hX₀.symm⟩
  have hLz : tangentSpaceMapArtinian.{u, v, w} g
      (e.hom.app (artinianDualNumbers.{u, w, v} Λ k) u₀) =
      e.hom.app (artinianDualNumbers.{u, w, v} Λ k) u₀ :=
    hinvbij.1 (by rwa [hL, hei])
  have hLinj : Function.Injective (tangentSpaceMapArtinian.{u, v, w} g) := fun y y' hyy' => by
    set z := e.hom.app (artinianDualNumbers.{u, w, v} Λ k) u₀ with hz
    have hw : tangentSpaceMapArtinian.{u, v, w} g (y - y' + z) = z := by
      rw [map_add, map_sub, hyy', sub_self, zero_add, hLz]
    have hx : (Hom.mapObjects f).app (artinianDualNumbers.{u, w, v} Λ k)
        (e.inv.app (artinianDualNumbers.{u, w, v} Λ k) (y - y' + z)) = u₀ := by
      rw [← hL, hw, hz, hei]
    have hker : quotientDifferential.{u, v, w} G
          (classOf (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
            (categoryOfElements_projection_isCofibered G.objects)
            (objectFiber (artinianDualNumbers.{u, w, v} Λ k)
              (e.inv.app (artinianDualNumbers.{u, w, v} Λ k) (y - y' + z)))) =
        quotientDifferential.{u, v, w} G
          (derivationToTangentSpace (Functor.Elements.π G.objects)
            (objects_isPredeformationCategory_of_isProrepresentable G hpro) 0) := by
      rw [← hX₀, quotientDifferential_classOf, quotientDifferential_classOf]
      exact classOf_quotientFiberObject_of_full f (artinianDualNumbers.{u, w, v} Λ k) _ u₀
        (by rw [hx, hu₀])
    have hfix := mapObjects_app_eq_of_mem_derivationRange G hpro f _
      (((isMinimal_iff_quotientDifferential_ker_le_derivationRange G hpro hsmooth).1 hmin)
        _ hker)
    have hzz : y - y' + z = z := hinvbij.1 (by rw [← hfix, hx, hz, hei])
    exact sub_eq_zero.mp (add_eq_right.mp hzz)
  have hϕ : (Hom.mapObjects f).app (artinianDualNumbers.{u, w, v} Λ k) =
      e.inv.app (artinianDualNumbers.{u, w, v} Λ k) ∘ tangentSpaceMapArtinian.{u, v, w} g ∘
        e.hom.app (artinianDualNumbers.{u, w, v} Λ k) :=
    funext fun x => by simp only [Function.comp_apply, hL, hei]
  rw [hϕ]
  exact hinvbij.comp
    ((show Function.Bijective (tangentSpaceMapArtinian.{u, v, w} g) from
      ⟨hLinj, LinearMap.injective_iff_surjective.1 hLinj⟩).comp
        ((isIso_iff_bijective _).1 inferInstance))

/-- An endomorphism of a minimal smooth prorepresentable groupoid in functors inducing an
equivalence of the quotient categories cofibered in groupoids is an isomorphism. -/
public theorem isIso_of_quotientMap_isEquivalence [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hpro : IsProrepresentable G) (hsmooth : IsSmooth G) (hmin : IsMinimal.{u, v, w, v} G)
    (f : G ⟶ G) [(quotientMap f).IsEquivalence] :
    IsIso f := by
  have hobj : ∀ A, Function.Bijective ((Hom.mapObjects f).app A) := by
    let _ : IsIso (Hom.mapObjects f) :=
      isIso_of_tangentSpace_bijective G.objects
        ((isProrepresentable_iff_objects_arrows G).1 hpro).1 (Hom.mapObjects f)
        (bijective_mapObjects_app_dualNumbers G hpro hsmooth hmin f)
    exact fun A => (isIso_iff_bijective ((Hom.mapObjects f).app A)).1 inferInstance
  refine isIso_of_bijective_components f hobj fun A => ?_
  let _ : (Hom.evaluation f A).Full := Hom.evaluation_full f A
  let _ : (Hom.evaluation f A).Faithful := Hom.evaluation_faithful f A
  exact Hom.mapArrows_app_bijective f A (hobj A)

/-- **Stacks Project, Tag 06KQ.** Let `(U, R, s, t, c)` be a minimal smooth prorepresentable
groupoid in functors on `𝒞_Λ`. An equivalence `[U/R] → [U/R]` of categories cofibered in
groupoids induced by an endomorphism of the groupoid is an isomorphism of categories. -/
@[stacks 06KQ "equivalence taken as induced by an endomorphism of the groupoid, and the \
conclusion read as strict isomorphism of categories. Neither is the source's reading, so this \
is an auxiliary and not the tag's covering declaration: the tag is carried outright by \
`Deformation.GroupoidInFunctors.exists_isIso_hom_of_isEquivalence_endo`, which takes an \
arbitrary 1-morphism of the quotients over 𝒞_Λ whose functor is an equivalence of categories \
and concludes that it is isomorphic to the one induced by an isomorphism of groupoids in \
functors. What this auxiliary adds is that the induced functor is then an isomorphism of \
categories on the nose, which is stronger than the source's conclusion and not invariant \
under isomorphism of functors"]
public theorem isIso_quotientMap_of_isEquivalence [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hpro : IsProrepresentable G) (hsmooth : IsSmooth G) (hmin : IsMinimal.{u, v, w, v} G)
    (f : G ⟶ G) [(quotientMap f).IsEquivalence] :
    IsIso (quotientMap f).toCatHom :=
  let _ := isIso_of_quotientMap_isEquivalence G hpro hsmooth hmin f
  isIso_quotientMap f

end GroupoidInFunctors

end

end Deformation
