module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyA
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
import all Mathlib.CategoryTheory.Limits.HasLimits
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison map for the stalk of a finite direct image

The finiteness of the set of lifts of a geometric point through a finite morphism, and the
comparison map `(f_* F)_y ⟶ ∏_{x ↦ y} F_x` from the stalk of a direct image to the product of
the stalks over the lifts: its components, its values on germs, its naturality in the sheaf, and
the product decomposition of the stalk assuming the comparison map is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

section Finiteness

/-- A finite scheme over a field has only finitely many sections: the sections correspond
injectively to algebra maps of its ring of global sections into the field, and that ring is
module-finite over the field. -/
private theorem finite_sections_of_isFinite_affine {X : Scheme.{u}} [IsAffine X]
    {Ω : Type u} [Field Ω] (f : X ⟶ Spec (.of Ω)) [IsFinite f] :
    Finite {g : Spec (.of Ω) ⟶ X // g ≫ f = 𝟙 _} := by
  let e := X.isoSpec
  suffices h : Finite {g : Spec (.of Ω) ⟶ Spec Γ(X, ⊤) // g ≫ (e.inv ≫ f) = 𝟙 _} from
    Finite.of_injective (fun g => (⟨g.1 ≫ e.hom, by simp [g.2]⟩ :
      {g : Spec (.of Ω) ⟶ Spec Γ(X, ⊤) // g ≫ (e.inv ≫ f) = 𝟙 _}))
      (fun a b h => Subtype.ext ((cancel_mono e.hom).mp (congrArg Subtype.val h)))
  let φ := Spec.homEquiv (e.inv ≫ f)
  have hf : IsFinite (Spec.map φ) := by
    show IsFinite (Spec.map (Spec.homEquiv (e.inv ≫ f)))
    simpa using (inferInstance : IsFinite (e.inv ≫ f))
  let := φ.hom.toAlgebra
  have : Module.Finite Ω Γ(X, ⊤) := (IsFinite.SpecMap_iff φ).mp hf
  let t (g : {g : Spec (.of Ω) ⟶ Spec Γ(X, ⊤) // g ≫ (e.inv ≫ f) = 𝟙 _}) :
      Γ(X, ⊤) →ₐ[Ω] Ω :=
    { __ := (Spec.homEquiv g.1).hom
      commutes' := by
        intro r
        have hg := congrArg (fun k => Spec.homEquiv k) g.2
        show ((Spec.homEquiv g.1).hom) (φ.hom r) = r
        simpa [φ] using congrArg (fun k => k.hom r) hg }
  exact Finite.of_injective t (by
    intro a b h
    refine Subtype.ext (Spec.homEquiv.injective ?_)
    ext r
    exact congrArg (fun k => k r) h)

/-- A finite morphism of schemes admits only finitely many lifts of a morphism from the
spectrum of a field. The lifts are the sections of the base change, which is a finite morphism
to the spectrum of the field. -/
public theorem finite_lifts_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ Y) :
    Finite {g : Spec (.of Ω) ⟶ X // g ≫ f = s} := by
  have : Finite {g : Spec (.of Ω) ⟶ pullback f s // g ≫ pullback.snd f s = 𝟙 _} :=
    finite_sections_of_isFinite_affine (pullback.snd f s)
  apply Finite.of_injective (fun g => (⟨pullback.lift g.1 (𝟙 _) (by simpa using g.2),
    pullback.lift_snd _ _ _⟩ :
      {g : Spec (.of Ω) ⟶ pullback f s // g ≫ pullback.snd f s = 𝟙 _}))
  intro a b h
  exact Subtype.ext <| (pullback.lift_fst _ _ _).symm.trans
    ((congrArg (fun g => g.1 ≫ pullback.fst f s) h).trans (pullback.lift_fst _ _ _))

/-- A finite morphism admits only finitely many lifts of a geometric point. -/
public instance finite_geometricPointLifts {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (y : GeometricPoint Y) :
    Finite {g : y.source ⟶ X // g ≫ f = y.hom} :=
  finite_lifts_of_isFinite f y.hom

end Finiteness

/-- A lift of a geometric point through a morphism, with unchanged residue field. -/
public abbrev geometricPointLift {X Y : Scheme.{u}} (f : X ⟶ Y) (y : GeometricPoint Y)
    (x : {g : y.source ⟶ X // g ≫ f = y.hom}) :
    GeometricPoint X :=
  { residueField := y.residueField, hom := x.1 }

/-- A lift of a geometric point lies over it. -/
public theorem geometricPointLift_map {X Y : Scheme.{u}} (f : X ⟶ Y) (y : GeometricPoint Y)
    (x : {g : y.source ⟶ X // g ≫ f = y.hom}) :
    (geometricPointLift f y x).map f = y :=
  congrArg (fun h : y.source ⟶ Y => ({ y with hom := h } : GeometricPoint Y)) x.property

section Component

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The canonical map from the stalk of a direct image at a geometric point `y` of the target
to the stalk at a geometric point `x` of the source lying over `y`.

The stalk at `x` of the inverse image of a sheaf on the target is the stalk of that sheaf at
`x`'s image (Tag 03Q1); applying this to the direct image `f_* F` and following with the stalk
at `x` of the counit `f^* f_* F ⟶ F` gives the map. -/
public def pushforwardEtaleStalkComponent
    (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    etaleStalk B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F).obj →
      etaleStalk B X.1 X.property x F.obj :=
  fun z =>
    (etaleStalkFunctor.{u, u + 1} B X.1 X.property x).map
      (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).counit.app F)
      ((smallEtalePullbackStalkIso B f x).inv.app
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F) (h.symm ▸ z))

/-- **The comparison on germs.** A section `s` of `F` over the base change `U ×_Y X` of an étale
neighborhood `U` of `y` — that is, a section of `f_* F` over `U` — has germ at `y` sent to the
germ at `x` of the restriction of `s` to any étale neighborhood `V` of `x` equipped with a map
to `U ×_Y X` compatible with the two points. -/
public theorem pushforwardEtaleStalkComponent_germ
    (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (V : (geometricPointFiber B X.1 X.property x).Elements)
    (t : V.1 ⟶ (smallEtaleBaseChange B f).obj U.1)
    (ht : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) =
      eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source) h) ≫ U.2.1)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj U.1))) :
    pushforwardEtaleStalkComponent B f x y h F
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj) (op U) s) =
      colimit.ι ((CategoryOfElements.π
        (geometricPointFiber B X.1 X.property x)).op ⋙ F.obj) (op V) (F.obj.map t.op s) := by
  subst y
  let adj := (smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)
  let P := ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F
  let D := (CategoryOfElements.π (geometricPointFiber B Y.1 Y.property
    (x.map (B.inclusion.map f)))).op ⋙ P.obj
  let L := ((smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj P
  let E := (CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ L.obj
  let Q := (CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ F.obj
  let e := (smallEtalePullbackStalkIso B f x).app P
  simp only [eqToHom_refl, Category.id_comp] at ht
  have hg := smallEtalePullbackStalkIso_germ B f x P V U t ht s
  have hi : e.inv (colimit.ι D (op U) s) =
      colimit.ι E (op V) (pullbackSectionAlong B f P U.1 V.1 t s) := by
    rw [← hg]
    exact ConcreteCategory.congr_hom e.hom_inv_id _
  show (etaleStalkFunctor.{u, u + 1} B X.1 X.property x).map (adj.counit.app F)
    (e.inv (colimit.ι D (op U) s)) = colimit.ι Q (op V) (F.obj.map t.op s)
  rw [hi]
  show (colimit.ι E (op V) ≫ colim.map
    (Functor.whiskerLeft (CategoryOfElements.π
      (geometricPointFiber B X.1 X.property x)).op (adj.counit.app F).hom)) _ = _
  rw [colimit.ι_map]
  show colimit.ι Q (op V)
    ((adj.counit.app F).hom.app (op V.1) (pullbackSectionAlong B f P U.1 V.1 t s)) = _
  congr 1
  unfold pullbackSectionAlong
  have hn := (adj.counit.app F).hom.naturality t.op
  have htri := congrArg (fun a => a.hom.app (op U.1)) (adj.right_triangle_components F)
  have hn' := ConcreteCategory.congr_hom hn
  have htri' := ConcreteCategory.congr_hom htri s
  dsimp at hn' htri'
  show (adj.counit.app F).hom.app (op V.1)
    (L.obj.map t.op ((adj.unit.app P).hom.app (op U.1) s)) = F.obj.map t.op s
  change (adj.counit.app F).hom.app (op ((smallEtaleBaseChange B f).obj U.1))
    ((adj.unit.app P).hom.app (op U.1) s) = s at htri'
  exact (hn' _).trans (congrArg (fun z => F.obj.map t.op z) htri')

/-- **Naturality of the comparison in the sheaf.** -/
public theorem pushforwardEtaleStalkComponent_natural
    (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    {F G : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))} (α : F ⟶ G)
    (z : etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj) :
    pushforwardEtaleStalkComponent B f x y h G
        ((etaleStalkFunctor.{u, u + 1} B Y.1 Y.property y).map
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).map α) z) =
      (etaleStalkFunctor.{u, u + 1} B X.1 X.property x).map α
        (pushforwardEtaleStalkComponent B f x y h F z) := by
  subst y
  let J := SmallEtale.topology B Y.1 Y.property
  let K := SmallEtale.topology B X.1 X.property
  let bc := smallEtaleBaseChange B f
  let PF := bc.sheafPushforwardContinuous (Type (u + 1)) J K
  let PB := bc.sheafPullback (Type (u + 1)) J K
  let adj := bc.sheafAdjunctionContinuous (Type (u + 1)) J K
  let SX := etaleStalkFunctor.{u, u + 1} B X.1 X.property x
  let SY := etaleStalkFunctor.{u, u + 1} B Y.1 Y.property (x.map (B.inclusion.map f))
  let iso := smallEtalePullbackStalkIso B f x
  have key : SY.map (PF.map α) ≫ iso.inv.app (PF.obj G) ≫ SX.map (adj.counit.app G) =
      iso.inv.app (PF.obj F) ≫ SX.map (adj.counit.app F) ≫ SX.map α := by
    rw [← Category.assoc, iso.inv.naturality (PF.map α), Category.assoc]
    congr 1
    show SX.map (PB.map (PF.map α)) ≫ SX.map (adj.counit.app G) = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg SX.map (adj.counit.naturality α)
  exact congrArg (fun k => k z) key

end Component

section Lifts

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)

/-- The canonical map from the stalk of a direct image at `y` to the stalk at one lift of `y`,
induced by the counit of inverse and direct image. This is
`AlgebraicGeometry.pushforwardEtaleStalkComponent` at the geometric point
`AlgebraicGeometry.geometricPointLift`. -/
public def finitePushforwardStalkComponent
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj →
    etaleStalk B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x) F.obj :=
  pushforwardEtaleStalkComponent B f (geometricPointLift (B.inclusion.map f) y x) y
    (geometricPointLift_map (B.inclusion.map f) y x) F

/-- The base change `U ×_Y X` of an étale neighborhood `U` of `y`, pointed by the lift of `y`
to `U ×_Y X` determined by a lift `x` of `y` to `X`: an étale neighborhood of `x`. -/
public def liftedEtaleNeighborhood
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (U : (geometricPointFiber B Y.1 Y.property y).Elements) :
    (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).Elements := by
  letI := hasPullbacks_bigEtaleSite B
  letI := preservesPullbacks_bigEtaleSiteInclusion B
  have hxy : x.1 ≫ B.inclusion.map f = U.2.1 ≫ B.inclusion.map U.1.obj.hom := by
    calc x.1 ≫ B.inclusion.map f = y.hom := x.2
      _ = U.2.1 ≫ B.inclusion.map U.1.obj.hom := U.2.2.symm
  refine Functor.elementsMk _ ((smallEtaleBaseChange B f).obj U.1)
    ⟨((IsPullback.of_hasPullback
        (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f).map B.inclusion).lift
      U.2.1 x.1 hxy.symm, ?_⟩
  change ((IsPullback.of_hasPullback
      (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f).map B.inclusion).lift
    U.2.1 x.1 hxy.symm ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1
  simp

/-- **The comparison on germs, at a lift.** The germ at `y` of a section `s` of `F` over the
base change `U ×_Y X` of an étale neighborhood `U` of `y` — that is, of a section of `f_* F`
over `U` — is sent to the germ of `s` at the pointed neighborhood
`AlgebraicGeometry.liftedEtaleNeighborhood`. -/
public theorem finitePushforwardStalkComponent_germ
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj U.1))) :
    finitePushforwardStalkComponent B f y F x
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).obj F).obj) (op U) s) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj)
        (op (liftedEtaleNeighborhood B f y x U)) s := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  have ht : (liftedEtaleNeighborhood B f y x U).2.1 ≫
      (SmallEtale.toScheme B X.1 X.property).map (𝟙 ((smallEtaleBaseChange B f).obj U.1)) ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) =
      eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source)
        (geometricPointLift_map (B.inclusion.map f) y x)) ≫ U.2.1 := by
    simp [liftedEtaleNeighborhood]
  have h := pushforwardEtaleStalkComponent_germ B f
    (geometricPointLift (B.inclusion.map f) y x) y
    (geometricPointLift_map (B.inclusion.map f) y x) F U
    (liftedEtaleNeighborhood B f y x U) (𝟙 _) ht s
  refine h.trans (congrArg (fun v => colimit.ι
    ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj)
    (op (liftedEtaleNeighborhood B f y x U)) v) ?_)
  exact ConcreteCategory.congr_hom
    (F.obj.map_id (op ((smallEtaleBaseChange B f).obj U.1))) s

/-- **The comparison map of Tag 03QP.** The stalk of a direct image at a geometric point maps
canonically to the product of the stalks over all lifts of that point. For a finite morphism
this map is bijective; that is the content of the tag and is not proved here. -/
public def finitePushforwardStalkToProduct
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj →
      (∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
        etaleStalk B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x) F.obj) :=
  fun z x => finitePushforwardStalkComponent B f y F x z

/-- Each component of the comparison map is the canonical stalk map. -/
public theorem finitePushforwardStalkToProduct_apply
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (z : etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    finitePushforwardStalkToProduct B f y F z x =
      finitePushforwardStalkComponent B f y F x z :=
  rfl

/-- **The comparison map on germs.** The germ at `y` of a section `s` of `f_* F` over an étale
neighborhood `U` has as its `x`-component the germ of `s` at the pointed étale neighborhood
`AlgebraicGeometry.liftedEtaleNeighborhood` of the lift `x`. -/
public theorem finitePushforwardStalkToProduct_germ
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj U.1)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    finitePushforwardStalkToProduct B f y F
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).obj F).obj) (op U) s) x =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj)
        (op (liftedEtaleNeighborhood B f y x U)) s :=
  finitePushforwardStalkComponent_germ B f y F x U s

/-- The comparison map is natural in the sheaf. -/
public theorem finitePushforwardStalkToProduct_natural
    {F G : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))} (α : F ⟶ G)
    (z : etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    finitePushforwardStalkToProduct B f y G
        ((etaleStalkFunctor.{u, u + 1} B Y.1 Y.property y).map
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).map α) z) x =
      (etaleStalkFunctor.{u, u + 1} B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).map α
        (finitePushforwardStalkToProduct B f y F z x) :=
  pushforwardEtaleStalkComponent_natural B f (geometricPointLift (B.inclusion.map f) y x) y
    (geometricPointLift_map (B.inclusion.map f) y x) α z

/-- **The product decomposition of the stalk, conditional on bijectivity.** Tag 03QP asserts
that the comparison map `AlgebraicGeometry.finitePushforwardStalkToProduct` is bijective when
`B.inclusion.map f` is finite; granted that, the stalk of the direct image *is* the product of
the stalks over the lifts. This declaration is strictly weaker than the tagged statement,
because bijectivity is a hypothesis rather than a conclusion. -/
public def finitePushforwardStalkEquivOfBijective
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (hbij : Function.Bijective (finitePushforwardStalkToProduct B f y F)) :
    etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj ≃
      (∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
        etaleStalk B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x) F.obj) :=
  Equiv.ofBijective _ hbij

/-- Each component of the conditional product equivalence is the canonical stalk map. -/
public theorem finitePushforwardStalkEquivOfBijective_apply
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (hbij : Function.Bijective (finitePushforwardStalkToProduct B f y F))
    (z : etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    finitePushforwardStalkEquivOfBijective B f y F hbij z x =
      finitePushforwardStalkComponent B f y F x z :=
  rfl

/-- The conditional product equivalence is natural in the sheaf. -/
public theorem finitePushforwardStalkEquivOfBijective_natural
    {F G : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))} (α : F ⟶ G)
    (hF : Function.Bijective (finitePushforwardStalkToProduct B f y F))
    (hG : Function.Bijective (finitePushforwardStalkToProduct B f y G))
    (z : etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    finitePushforwardStalkEquivOfBijective B f y G hG
        ((etaleStalkFunctor.{u, u + 1} B Y.1 Y.property y).map
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).map α) z) x =
      (etaleStalkFunctor.{u, u + 1} B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).map α
        (finitePushforwardStalkEquivOfBijective B f y F hF z x) :=
  finitePushforwardStalkToProduct_natural B f y α z x

end Lifts

end AlgebraicGeometry

end
