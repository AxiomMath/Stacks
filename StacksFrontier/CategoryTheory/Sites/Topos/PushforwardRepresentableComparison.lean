module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Recognising the direct image of a morphism of topoi from its inverse image on representables

Let `J` and `K` be subcanonical topologies on categories `C` and `D`, let `g : Sh(D) ⟶ Sh(C)` be a
morphism of topoi and let `u : C ⥤ D` be a continuous functor.  If the inverse image of `g` carries
the representable sheaf `h_V` of an object `V` of `C` to the representable sheaf `h_{u V}`,
naturally in `V`, then the direct image of `g` is the direct image `u^s` of the continuous functor:

`g_* ≅ u^s`.

Sections of a sheaf over an object are maps out of the representable sheaf of that object — this is
where subcanonicity is used — so for a sheaf `F` on `D` and an object `V` of `C`

`(g_*F)(V) = Mor(h_V, g_*F) = Mor(g⁻¹h_V, F) = Mor(h_{u V}, F) = F(u V) = (u^s F)(V)`,

the first and last steps by Yoneda, the second by the adjunction `g⁻¹ ⊣ g_*` and the third by the
assumed isomorphism.  Each step is natural in `F` and in `V`, so the composite is an isomorphism of
functors.

## Main definitions

* `MorphismOfTopoi.representableSectionsEquivOfIso` — the bijection `(g_*F)(V) ≃ F(u V)` above out
  of a comparison of representables at the single object `V`, together with its naturality in `V`
  at each morphism whose naturality square commutes.
* `MorphismOfTopoi.representableSectionsEquiv` — the bijection `(g_*F)(V) ≃ F(u V)` above, for one
  sheaf `F` and one object `V`.
* `MorphismOfTopoi.pushforwardIsoSheafPushforwardContinuous` — the isomorphism of functors
  `g_* ≅ u^s` it assembles into.

## Implementation notes

The hypothesis is an isomorphism of functors `C ⥤ Sh(D)`, namely `J.yoneda ⋙ g⁻¹ ≅ u ⋙ K.yoneda`;
its naturality in `V` is what makes the bijections above natural in `V`, and without it the
conclusion would be a family of bijections of sections rather than an isomorphism of sheaves.

Nothing here is specific to the étale setting, and no hypothesis beyond continuity is placed on
`u`: the content is that a morphism of topoi is recognised, on direct images, by what its inverse
image does to representables.

Sheaves take values in `Type w`, the universe of the morphisms of the two sites; the object
universes are unconstrained, so that the small étale site — whose objects are étale charts, a
`Type (u+1)`, and whose morphisms and sections live in `Type u` — is covered.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u₁ u₂

namespace MorphismOfTopoi

variable {C : Type u₁} [Category.{w} C] {D : Type u₂} [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.Subcanonical] [K.Subcanonical]
  (g : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w)))
  {u : C ⥤ D} [u.IsContinuous J K]
  (α : J.yoneda ⋙ g.inverseImage ≅ u ⋙ K.yoneda)

/-! ### The computation at a single object

The bijection `(g_*F)(V) ≃ F(u V)` uses `α` only through its component at `V`, and its naturality
in `V` only through the naturality square of `α` at the morphism in question.  It is therefore
stated below for a bare isomorphism `e : g⁻¹h_V ≅ h_{u V}`, with the naturality square as a
hypothesis, so that it applies when such an isomorphism is available at *some* of the objects of
`C` only. -/

/-- Precomposition with an isomorphism `g⁻¹h_V ≅ h_{u V}`, as a bijection of hom-sets
`Mor(g⁻¹h_V, F) ≃ Mor(h_{u V}, F)`. -/
def precompIsoEquiv (F : Sheaf K (Type w)) {V : C}
    (e : g.inverseImage.obj (J.yoneda.obj V) ≅ K.yoneda.obj (u.obj V)) :
    (g.inverseImage.obj (J.yoneda.obj V) ⟶ F) ≃ (K.yoneda.obj (u.obj V) ⟶ F) where
  toFun h := e.inv ≫ h
  invFun h := e.hom ≫ h
  left_inv h := by
    show e.hom ≫ e.inv ≫ h = h
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  right_inv h := by
    show e.inv ≫ e.hom ≫ h = h
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- **The sections of the direct image at one object, computed through a comparison of
representables there.**  For a sheaf `F` on `D`, an object `V` of `C` and an isomorphism
`e : g⁻¹h_V ≅ h_{u V}`, the sections of `g_*F` over `V` are the sections of `F` over `u V`: both
are maps out of a representable sheaf, and the two representables correspond under `e`. -/
def representableSectionsEquivOfIso (F : Sheaf K (Type w)) {V : C}
    (e : g.inverseImage.obj (J.yoneda.obj V) ≅ K.yoneda.obj (u.obj V)) :
    (g.pushforward.obj F).obj.obj (op V) ≃ F.obj.obj (op (u.obj V)) :=
  ((J.yonedaEquiv (X := V) (F := g.pushforward.obj F)).symm.trans
      ((g.adj.homEquiv (J.yoneda.obj V) F).symm)).trans
    ((precompIsoEquiv g F e).trans (K.yonedaEquiv (X := u.obj V) (F := F)))

/-- The bijection of `MorphismOfTopoi.representableSectionsEquivOfIso` sends a section `x` of
`g_*F` over `V` to the section of `F` over `u V` obtained by transporting `x` to a morphism
`g⁻¹h_V ⟶ F` along Yoneda and the adjunction, precomposing with `e.inv`, and reading the resulting
morphism `h_{u V} ⟶ F` as a section by Yoneda. -/
theorem representableSectionsEquivOfIso_apply (F : Sheaf K (Type w)) {V : C}
    (e : g.inverseImage.obj (J.yoneda.obj V) ≅ K.yoneda.obj (u.obj V))
    (x : (g.pushforward.obj F).obj.obj (op V)) :
    representableSectionsEquivOfIso g F e x =
      K.yonedaEquiv (e.inv ≫
        (g.adj.homEquiv (J.yoneda.obj V) F).symm (J.yonedaEquiv.symm x)) :=
  rfl

/-- The inverse of the bijection of `MorphismOfTopoi.representableSectionsEquivOfIso`: a section of
`F` over `u V` is read as a section of `g_*F` over `V` by taking its Yoneda morphism, precomposing
with `e` and transporting back along the adjunction and Yoneda. -/
theorem representableSectionsEquivOfIso_symm_apply (F : Sheaf K (Type w)) {V : C}
    (e : g.inverseImage.obj (J.yoneda.obj V) ≅ K.yoneda.obj (u.obj V))
    (w : F.obj.obj (op (u.obj V))) :
    (representableSectionsEquivOfIso g F e).symm w =
      J.yonedaEquiv (g.adj.homEquiv (J.yoneda.obj V) F (e.hom ≫ K.yonedaEquiv.symm w)) :=
  rfl

/-- **The bijection of `MorphismOfTopoi.representableSectionsEquivOfIso` is natural in the
object**, at every morphism `k` whose naturality square for the chosen isomorphisms commutes. -/
theorem representableSectionsEquivOfIso_naturality (F : Sheaf K (Type w)) {V V' : C} (k : V' ⟶ V)
    {e : g.inverseImage.obj (J.yoneda.obj V) ≅ K.yoneda.obj (u.obj V)}
    {e' : g.inverseImage.obj (J.yoneda.obj V') ≅ K.yoneda.obj (u.obj V')}
    (hnat : e'.inv ≫ g.inverseImage.map (J.yoneda.map k) = K.yoneda.map (u.map k) ≫ e.inv)
    (x : (g.pushforward.obj F).obj.obj (op V)) :
    representableSectionsEquivOfIso g F e' ((g.pushforward.obj F).obj.map k.op x) =
      F.obj.map (u.map k).op (representableSectionsEquivOfIso g F e x) := by
  rw [representableSectionsEquivOfIso_apply, representableSectionsEquivOfIso_apply,
    GrothendieckTopology.yonedaEquiv_symm_map, g.adj.homEquiv_naturality_left_symm]
  simp only [Quiver.Hom.unop_op, Opposite.unop_op]
  rw [← Category.assoc, hnat, Category.assoc,
    ← GrothendieckTopology.yonedaEquiv_naturality]

/-- The bijection of `MorphismOfTopoi.representableSectionsEquivOfIso` is natural in the sheaf
`F`. -/
theorem representableSectionsEquivOfIso_naturality_sheaf {F F' : Sheaf K (Type w)} (β : F ⟶ F')
    {V : C} (e : g.inverseImage.obj (J.yoneda.obj V) ≅ K.yoneda.obj (u.obj V))
    (x : (g.pushforward.obj F).obj.obj (op V)) :
    representableSectionsEquivOfIso g F' e ((g.pushforward.map β).hom.app (op V) x) =
      β.hom.app (op (u.obj V)) (representableSectionsEquivOfIso g F e x) := by
  rw [representableSectionsEquivOfIso_apply, representableSectionsEquivOfIso_apply,
    ← GrothendieckTopology.yonedaEquiv_comp]
  congr 1
  rw [← GrothendieckTopology.yonedaEquiv_symm_naturality_right,
    g.adj.homEquiv_naturality_right_symm, ← Category.assoc]

/-! ### The comparison at every object -/

/-- Precomposition with the component of `α` at `V`, as a bijection of hom-sets
`Mor(g⁻¹h_V, F) ≃ Mor(h_{u V}, F)`. -/
def precompAlphaEquiv (F : Sheaf K (Type w)) (V : C) :
    (g.inverseImage.obj (J.yoneda.obj V) ⟶ F) ≃ (K.yoneda.obj (u.obj V) ⟶ F) :=
  precompIsoEquiv g F (α.app V)

/-- **The sections of the direct image, computed through the inverse image of a representable.**
For a sheaf `F` on `D` and an object `V` of `C`, the sections of `g_*F` over `V` are the sections
of `F` over `u V`: both are maps out of a representable sheaf, and the two representables
correspond under `α`. -/
def representableSectionsEquiv (F : Sheaf K (Type w)) (V : C) :
    (g.pushforward.obj F).obj.obj (op V) ≃ F.obj.obj (op (u.obj V)) :=
  representableSectionsEquivOfIso g F (α.app V)

/-- The bijection of `MorphismOfTopoi.representableSectionsEquiv` sends a section `x` of `g_*F`
over `V` to the section of `F` over `u V` obtained by transporting `x` to a morphism `g⁻¹h_V ⟶ F`
along Yoneda and the adjunction, precomposing with the component of `α.inv` at `V`, and reading the
resulting morphism `h_{u V} ⟶ F` as a section by Yoneda. -/
theorem representableSectionsEquiv_apply (F : Sheaf K (Type w)) (V : C)
    (x : (g.pushforward.obj F).obj.obj (op V)) :
    representableSectionsEquiv g α F V x =
      K.yonedaEquiv (α.inv.app V ≫
        (g.adj.homEquiv (J.yoneda.obj V) F).symm (J.yonedaEquiv.symm x)) :=
  rfl

/-- The bijection of `MorphismOfTopoi.representableSectionsEquiv` is natural in the object `V`. -/
theorem representableSectionsEquiv_naturality (F : Sheaf K (Type w)) {V V' : C} (k : V' ⟶ V)
    (x : (g.pushforward.obj F).obj.obj (op V)) :
    representableSectionsEquiv g α F V' ((g.pushforward.obj F).obj.map k.op x) =
      F.obj.map (u.map k).op (representableSectionsEquiv g α F V x) :=
  representableSectionsEquivOfIso_naturality g F k (α.inv.naturality k).symm x

/-- The bijection of `MorphismOfTopoi.representableSectionsEquiv` is natural in the sheaf `F`. -/
theorem representableSectionsEquiv_naturality_sheaf {F F' : Sheaf K (Type w)} (β : F ⟶ F')
    (V : C) (x : (g.pushforward.obj F).obj.obj (op V)) :
    representableSectionsEquiv g α F' V ((g.pushforward.map β).hom.app (op V) x) =
      β.hom.app (op (u.obj V)) (representableSectionsEquiv g α F V x) :=
  representableSectionsEquivOfIso_naturality_sheaf g β (α.app V) x

/-- The sections bijections assemble into an isomorphism of sheaves `g_*F ≅ u^s F`. -/
def pushforwardObjIso (F : Sheaf K (Type w)) :
    g.pushforward.obj F ≅ (u.sheafPushforwardContinuous (Type w) J K).obj F :=
  (fullyFaithfulSheafToPresheaf J (Type w)).preimageIso
    (NatIso.ofComponents (fun V => Equiv.toIso (representableSectionsEquiv g α F V.unop))
      (fun {V V'} k => by
        ext x
        exact representableSectionsEquiv_naturality g α F k.unop x))

/-- **A morphism of topoi whose inverse image matches a continuous functor on representables has
that functor's direct image.**  If `g⁻¹h_V ≅ h_{u V}` naturally in `V`, then `g_* ≅ u^s`. -/
def pushforwardIsoSheafPushforwardContinuous :
    g.pushforward ≅ u.sheafPushforwardContinuous (Type w) J K :=
  NatIso.ofComponents (pushforwardObjIso g α) (fun {F F'} β => by
    ext V x
    exact representableSectionsEquiv_naturality_sheaf g α β V.unop x)

/-- The component of `MorphismOfTopoi.pushforwardIsoSheafPushforwardContinuous` at a sheaf `F` acts
on the sections over an object `V` as the bijection
`MorphismOfTopoi.representableSectionsEquiv`. -/
@[simp]
theorem pushforwardIsoSheafPushforwardContinuous_hom_app_hom_app
    (F : Sheaf K (Type w)) (V : Cᵒᵖ)
    (x : (g.pushforward.obj F).obj.obj V) :
    ((pushforwardIsoSheafPushforwardContinuous g α).hom.app F).hom.app V x =
      representableSectionsEquiv g α F V.unop x :=
  rfl

end MorphismOfTopoi

end
