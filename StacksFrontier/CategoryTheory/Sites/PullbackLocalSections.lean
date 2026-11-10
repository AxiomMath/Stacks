module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Local description of the sections of an inverse image of sheaves

Let `G : C ⥤ D` be a continuous functor of sites and let `L` be a left adjoint of the
pushforward `G.sheafPushforwardContinuous`, that is, an inverse-image functor on sheaves of
types. For a sheaf `F` on `C`, every section of `L.obj F` over an object `U` of `D` becomes,
after restriction along a covering sieve of `U`, the restriction of a section of `F` under the
adjunction unit: it is the restriction along some `h : V ⟶ G.obj W` of the image of a section
of `F` over `W`.

## Main definitions

* `CategoryTheory.Functor.unitSection`: the image of a section of `F` over `W` under the
  adjunction unit, as a section of `L.obj F` over `G.obj W`.
* `CategoryTheory.Functor.unitImage`: the subpresheaf of `L.obj F` cut out by the sections that
  are, on the nose, restrictions of unit sections.

## Main results

* `CategoryTheory.Functor.unitImage_sieveOfSection_mem`: the sieve on which a section of
  `L.obj F` is a restriction of a unit section is a covering sieve.
* `CategoryTheory.Functor.exists_locally_unit_section`: the same statement with explicit
  witnesses.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
  (adj : L ⊣ G.sheafPushforwardContinuous (Type w) J K)
  (F : Sheaf J (Type w))

/-- The image of a section of `F` over `W` under the adjunction unit, as a section of `L.obj F`
over `G.obj W`. -/
public def unitSection (W : C) (t : F.obj.obj (op W)) : (L.obj F).obj.obj (op (G.obj W)) :=
  (adj.unit.app F).hom.app (op W) t

/-- The adjunction unit is natural in the object of `C`. -/
public lemma unitSection_map {W W' : C} (k : W' ⟶ W) (t : F.obj.obj (op W)) :
    (L.obj F).obj.map (G.map k).op (unitSection G J K adj F W t) =
      unitSection G J K adj F W' (F.obj.map k.op t) :=
  (NatTrans.naturality_apply (adj.unit.app F).hom k.op t).symm

/-- The subpresheaf of `L.obj F` of those sections that are restrictions of sections of `F`
along the adjunction unit. -/
public def unitImage : Subfunctor (L.obj F).obj where
  obj U := {s | ∃ (W : C) (h : U.unop ⟶ G.obj W) (t : F.obj.obj (op W)),
    s = (L.obj F).obj.map h.op (unitSection G J K adj F W t)}
  map := by
    rintro U V i s ⟨W, h, t, rfl⟩
    refine ⟨W, i.unop ≫ h, t, ?_⟩
    rw [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]

/-- The sheafification of `CategoryTheory.Functor.unitImage` inside `L.obj F`: the sections
that lie in it locally, as a sheaf. -/
private def unitImageSheaf : Sheaf K (Type w) :=
  ⟨((unitImage G J K adj F).sheafify K).toFunctor,
    (isSheaf_iff_isSheaf_of_type K _).mpr
      ((unitImage G J K adj F).sheafify_isSheaf
        ((isSheaf_iff_isSheaf_of_type K _).mp (L.obj F).property))⟩

/-- The inclusion of the sheafified subpresheaf into `L.obj F`. -/
private def unitImageSheafι : unitImageSheaf G J K adj F ⟶ L.obj F :=
  ObjectProperty.homMk ((unitImage G J K adj F).sheafify K).ι

/-- The adjunction unit, lifted through the inclusion: a section of `F` over `W` gives a
section of the sheafified subpresheaf over `G.obj W`. -/
private def unitImageLift :
    F ⟶ (G.sheafPushforwardContinuous (Type w) J K).obj (unitImageSheaf G J K adj F) :=
  ObjectProperty.homMk
    { app X := ↾fun t ↦ ⟨unitSection G J K adj F X.unop t,
        (unitImage G J K adj F).le_sheafify K _
          ⟨X.unop, 𝟙 (G.obj X.unop), t,
            ((L.obj F).obj.map_id_apply (op (G.obj X.unop)) _).symm⟩⟩
      naturality := by
        intro X Y f
        ext t
        exact Subtype.ext (unitSection_map G J K adj F f.unop t).symm }

/-- Composing the lifted unit with the inclusion recovers the unit. -/
private theorem unitImageLift_comp :
    unitImageLift G J K adj F ≫
        (G.sheafPushforwardContinuous (Type w) J K).map (unitImageSheafι G J K adj F) =
      adj.unit.app F := by
  apply ObjectProperty.hom_ext
  ext X t
  rfl

/-- The retraction of the inclusion furnished by the adjunction: the transpose of the lifted
unit. -/
private def unitImageRetraction : L.obj F ⟶ unitImageSheaf G J K adj F :=
  (adj.homEquiv F (unitImageSheaf G J K adj F)).symm (unitImageLift G J K adj F)

/-- The transpose of the lifted unit is a retraction of the inclusion. -/
private theorem unitImageRetraction_comp :
    unitImageRetraction G J K adj F ≫ unitImageSheafι G J K adj F = 𝟙 (L.obj F) := by
  apply (adj.homEquiv F (L.obj F)).injective
  have h : adj.homEquiv F (L.obj F)
      (unitImageRetraction G J K adj F ≫ unitImageSheafι G J K adj F) = adj.unit.app F := by
    rw [adj.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← adj.homEquiv_unit]
    change adj.homEquiv F (unitImageSheaf G J K adj F)
        ((adj.homEquiv F (unitImageSheaf G J K adj F)).symm
          (unitImageLift G J K adj F)) ≫ _ = _
    rw [Equiv.apply_symm_apply, unitImageLift_comp]
  rw [h, adj.homEquiv_unit]
  simp

/-- Every section of `L.obj F` lies locally in `CategoryTheory.Functor.unitImage`: the sieve of
those restrictions of a section which are restrictions of unit sections is a covering sieve. -/
public theorem unitImage_sieveOfSection_mem (U : D) (s : (L.obj F).obj.obj (op U)) :
    (unitImage G J K adj F).sieveOfSection s ∈ K U := by
  have key : (unitImageSheafι G J K adj F).hom.app (op U)
      ((unitImageRetraction G J K adj F).hom.app (op U) s) = s := by
    simpa using congrArg (fun φ : L.obj F ⟶ L.obj F ↦ φ.hom.app (op U) s)
      (unitImageRetraction_comp G J K adj F)
  have hmem := ((unitImageRetraction G J K adj F).hom.app (op U) s).property
  rwa [show ((unitImageRetraction G J K adj F).hom.app (op U) s).val = s from key] at hmem

/-- Let `L` be an inverse-image functor on sheaves of types for a continuous functor
`G : C ⥤ D`, let `F` be a sheaf on `C` and let `s` be a section of `L.obj F` over an object `U`
of `D`. Then there is a covering sieve of `U` such that for every arrow `k : V ⟶ U` of it the
restriction of `s` along `k` is the restriction, along some `h : V ⟶ G.obj W` with `W` an object
of `C`, of the image under the adjunction unit of a section of `F` over `W`. -/
public theorem exists_locally_unit_section (U : D) (s : (L.obj F).obj.obj (op U)) :
    ∃ R : Sieve U, R ∈ K U ∧ ∀ ⦃V : D⦄ (k : V ⟶ U), R k →
      ∃ (W : C) (h : V ⟶ G.obj W) (t : F.obj.obj (op W)),
        (L.obj F).obj.map k.op s =
          (L.obj F).obj.map h.op (unitSection G J K adj F W t) :=
  ⟨(unitImage G J K adj F).sieveOfSection s,
    unitImage_sieveOfSection_mem G J K adj F U s, fun _ _ hk ↦ hk⟩

end CategoryTheory.Functor

end
