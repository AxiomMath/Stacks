module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryStalkFrobenius
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.RestrictionOfGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationDirectImageStalk

/-!
# Germs of pulled-back sections and the Frobenius on a boundary stalk

For `i : Z ⟶ X` and a geometric point `s` of `Z`, the identification `(i⁻¹ F)_s ≅ F_{s ≫ i}` of
Tag 03Q1 sends the germ at `s` of the pull-back of a section `σ` of `F` to the germ of `σ` at
`s ≫ i` (the germ formula of 03Q1). Over a strictly henselian local base this turns the map of
stalks induced by a morphism of geometric points into pull-back of global sections along an
endomorphism of the strict henselization: the Frobenius on the stalk of `j_* F` at a boundary
point (Weil II 1.8) is pull-back along the lift `β` of the Frobenius to `Spec 𝒪^{sh}`.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImageStalkIso_hom_germ_unit` — the germ formula.
* `AlgebraicGeometry.smallEtaleGlobalSectionsComparison_sheafFiberClosedPointIsoGamma_inv` — its
  form at closed geometric points of strictly henselian local schemes: the germ of the pull-back
  of a global section is the germ of the section.
* `AlgebraicGeometry.smallEtaleInverseImageStalkIso_comp` — the identifications of 03Q1 are
  compatible with `g⁻¹ h⁻¹ ≅ (g ≫ h)⁻¹`.
* `AlgebraicGeometry.closedPointStalkIsoGamma_hom_app_pullback` — through the identifications
  `F_{y ≫ π} ≅ Γ(Spec R, π⁻¹ F)` at closed geometric points of a strictly henselian local scheme,
  the map of stalks induced by `a` with `a ≫ y' = y ≫ β` is pull-back of global sections along
  `β`; for `β` an endomorphism of the strict henselization lifting a Frobenius, this computes the
  Frobenius on the stalk.
* `AlgebraicGeometry.smallEtalePointHom_sheafFiber_comp_stalkIsoStrictHenselizationGamma_hom` —
  the identification `F_s ≅ Γ(Spec 𝒪^{sh}_{S,s}, π⁻¹ F)` carries the 04FN map of an endomorphism
  `a` of `s` to `strictHenselizationSectionsPullback`, pull-back along the induced endomorphism of
  the strict henselization.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme

universe v u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

variable {Z X : Scheme.{u}} (i : Z ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Z)

/-- **`pointSmallEtaleHom` is the morphism of points of Tag 04FN** attached to the morphism of
geometric points `a`, `AlgebraicGeometry.smallEtalePointHom` (through which the Galois
action and the geometric Frobenius on stalks are computed). -/
theorem pointSmallEtaleHom_eq_smallEtalePointHom {T : Scheme.{u}} {Ω' : Type u} [Field Ω']
    [IsAlgClosed Ω'] (t t' : Spec (.of Ω') ⟶ T) (a : Spec (.of Ω') ⟶ Spec (.of Ω'))
    (ha : a ≫ t' = t) :
    pointSmallEtaleHom t t' a ha =
      AlgebraicGeometry.smallEtalePointHom T
        (⟨a, ha⟩ : GeometricPoint.Hom ⟨Ω', t⟩ ⟨Ω', t'⟩) :=
  rfl

/-- **The germ formula of Tag 03Q1**: the identification `(i⁻¹ F)_s ≅ F_{s ≫ i}` sends the germ
at `s` of the pull-back (by the unit of `i⁻¹ ⊣ i_*`) of a section `σ` over `V` to the germ of `σ`
at `(V, x)`, where `x` is the lift of `s ≫ i` to `V` matching the lift of `s` to `V ×_X Z`. -/
theorem smallEtaleInverseImageStalkIso_hom_germ_unit
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) (V : X.Etale)
    (x : (pointSmallEtale (s ≫ i)).fiber.obj V) :
    ((smallEtaleInverseImageAdjunction.{u, v} i).unit.app F).hom.app (op V) ≫
        (pointSmallEtale s).toPresheafFiber ((Stacks.EtaleCohomology.smallEtaleBaseChange i).obj V)
          ((pointSmallEtaleBaseChangeFiberIso i s).hom.app V x)
          ((smallEtaleInverseImage.{u, v} i).obj F).obj ≫
        (smallEtaleInverseImageStalkIso.{v, u} i s).hom.app F =
      (pointSmallEtale (s ≫ i)).toPresheafFiber V x F.obj := by
  have hunit : ((smallEtaleInverseImageAdjunction.{u, v} i).unit.app F).hom.app (op V) =
      ((Stacks.EtaleCohomology.smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op V) ≫
        (CategoryTheory.toSheafify (smallEtaleTopology Z)
          ((Stacks.EtaleCohomology.smallEtaleBaseChange i).op.lan.obj F.obj)).app
            (op ((Stacks.EtaleCohomology.smallEtaleBaseChange i).obj V)) := by
    simp [smallEtaleInverseImageAdjunction,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous, Adjunction.restrictFullyFaithful]
    rfl
  let G := Stacks.EtaleCohomology.smallEtaleBaseChange i
  let P := (sheafToPresheaf (smallEtaleTopology X) (Type (max (u + 1) v))).obj F
  let ex := (pointSmallEtaleBaseChangeFiberIso i s).hom.app V x
  let toSh := CategoryTheory.toSheafify (smallEtaleTopology Z) (G.op.lan.obj P)
  have hL : (pointSmallEtale (s ≫ i)).toPresheafFiber V x P ≫
      (GrothendieckTopology.Point.presheafFiberLanIso.{u, max (u + 1) v}
        (pointSmallEtale (s ≫ i)) (pointSmallEtale s) G
        (pointSmallEtaleBaseChangeFiberIso i s)).inv.app P =
      (G.op.lanUnit.app P).app (op V) ≫
        (pointSmallEtale s).toPresheafFiber (G.obj V) ex (G.op.lan.obj P) :=
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberLanIso_inv_app.{u, max (u + 1) v}
      (pointSmallEtale (s ≫ i)) (pointSmallEtale s) G (pointSmallEtaleBaseChangeFiberIso i s) P V x
  have hS : toSh.app (op (G.obj V)) ≫
      (pointSmallEtale s).toPresheafFiber (G.obj V) ex
        ((smallEtaleInverseImage.{u, v} i).obj F).obj =
      (pointSmallEtale s).toPresheafFiber (G.obj V) ex (G.op.lan.obj P) ≫
        (pointSmallEtale s).presheafFiber.map toSh :=
    ((pointSmallEtale s).toPresheafFiber_naturality toSh (G.obj V) ex).symm
  have hI : (pointSmallEtale s).presheafFiber.map toSh ≫
      ((pointSmallEtale s).presheafToSheafCompSheafFiberIso (Type (max (u + 1) v))).hom.app
        (G.op.lan.obj P) = 𝟙 _ :=
    Iso.inv_hom_id_app ((pointSmallEtale s).presheafToSheafCompSheafFiberIso (Type (max (u + 1) v)))
      (G.op.lan.obj P)
  let Lan := GrothendieckTopology.Point.presheafFiberLanIso.{u, max (u + 1) v}
    (pointSmallEtale (s ≫ i)) (pointSmallEtale s) G (pointSmallEtaleBaseChangeFiberIso i s)
  let I1 := ((pointSmallEtale s).presheafToSheafCompSheafFiberIso (Type (max (u + 1) v))).hom.app
    (G.op.lan.obj P)
  change ((smallEtaleInverseImageAdjunction.{u, v} i).unit.app F).hom.app (op V) ≫
      (pointSmallEtale s).toPresheafFiber (G.obj V) ex
          ((smallEtaleInverseImage.{u, v} i).obj F).obj ≫
        I1 ≫ Lan.hom.app P = _
  rw [hunit]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (I1 ≫ Lan.hom.app P)) hS).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ Lan.hom.app P) hI).trans (Category.id_comp _)))))))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ Lan.hom.app P) hL.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (_ ≫ ·) (Lan.inv_hom_id_app P)).trans (Category.comp_id _)

/-- **The units of inverse image along a composite**: pulling back a section along `h` and then
along `g`, and applying `smallEtaleInverseImageComp g h`, is pulling it back along `g ≫ h`,
read on `V ×_{T''} T' ×_{T'} T ≅ V ×_{T''} T`. -/
theorem smallEtaleInverseImageComp_unit {T T' T'' : Scheme.{u}} (g : T ⟶ T') (h : T' ⟶ T'')
    (F : Sheaf (smallEtaleTopology T'') (Type (max (u + 1) v))) (V : T''.Etale) :
    ((smallEtaleInverseImageAdjunction.{u, v} h).unit.app F).hom.app (op V) ≫
      ((smallEtaleInverseImageAdjunction.{u, v} g).unit.app
        ((smallEtaleInverseImage.{u, v} h).obj F)).hom.app
          (op ((Stacks.EtaleCohomology.smallEtaleBaseChange h).obj V)) ≫
      ((smallEtaleInverseImageComp.{u, v} g h).hom.app F).hom.app
        (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
          ((Stacks.EtaleCohomology.smallEtaleBaseChange h).obj V))) =
    ((smallEtaleInverseImageAdjunction.{u, v} (g ≫ h)).unit.app F).hom.app (op V) ≫
      ((smallEtaleInverseImage.{u, v} (g ≫ h)).obj F).obj.map
        ((smallEtaleBaseChangeComp g h).inv.app V).op := by
  have h' := congrArg (fun m => m.hom.app (op V)) (unit_conjugateEquiv_symm
    (smallEtaleInverseImageAdjunction.{u, v} (g ≫ h))
    ((smallEtaleInverseImageAdjunction.{u, v} h).comp (smallEtaleInverseImageAdjunction.{u, v} g))
    (smallEtalePushforwardCompIso.{u, v} g h).inv F)
  change ((smallEtaleInverseImageAdjunction.{u, v} (g ≫ h)).unit.app F).hom.app (op V) ≫
      ((smallEtalePushforwardCompIso.{u, v} g h).inv.app
        ((smallEtaleInverseImage.{u, v} (g ≫ h)).obj F)).hom.app (op V) =
    (((smallEtaleInverseImageAdjunction.{u, v} h).comp
      (smallEtaleInverseImageAdjunction.{u, v} g)).unit.app F).hom.app (op V) ≫
      ((smallEtaleInverseImageComp.{u, v} g h).hom.app F).hom.app
        (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
          ((Stacks.EtaleCohomology.smallEtaleBaseChange h).obj V))) at h'
  rw [Adjunction.comp_unit_app] at h'
  rw [smallEtalePushforwardCompIso, Functor.sheafPushforwardContinuousComp'_inv_app_hom_app] at h'
  exact (Category.assoc _ _ _).symm.trans h'.symm

private theorem comp_comp_hom_inv {𝒞 : Type*} [Category* 𝒞] {a b c d : 𝒞} (A : a ⟶ b) (B : b ⟶ c)
    (e : c ≅ d) : (A ≫ B ≫ e.hom) ≫ e.inv = A ≫ B := by
  simp

/-- **Germs at a geometric point move along an equality of geometric points.** -/
theorem toPresheafFiber_comp_eqToHom {T : Scheme.{u}} {t t' : Spec (.of Ω) ⟶ T} (e : t = t')
    (V : T.Etale) (x : (pointSmallEtale t).fiber.obj V) (P : T.Etaleᵒᵖ ⥤ Type (max (u + 1) v)) :
    (pointSmallEtale t).toPresheafFiber V x P ≫
        eqToHom (congrArg (fun k => (pointSmallEtale k).presheafFiber.obj P) e) =
      (pointSmallEtale t').toPresheafFiber V
        (CategoryTheory.Over.homMk x.left (by rw [← e]; exact CategoryTheory.Over.w x)) P := by
  subst e
  rfl

/-- The germ formula of Tag 03Q1, read backwards: the inverse of `(i⁻¹ F)_s ≅ F_{s ≫ i}` sends the
germ of `σ` at `(V, x)` to the germ of `i^* σ` at the matching lift of `s`. -/
theorem toPresheafFiber_smallEtaleInverseImageStalkIso_inv
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) (V : X.Etale)
    (x : (pointSmallEtale (s ≫ i)).fiber.obj V) :
    (pointSmallEtale (s ≫ i)).toPresheafFiber V x F.obj ≫
        (smallEtaleInverseImageStalkIso.{v, u} i s).inv.app F =
      ((smallEtaleInverseImageAdjunction.{u, v} i).unit.app F).hom.app (op V) ≫
        (pointSmallEtale s).toPresheafFiber ((Stacks.EtaleCohomology.smallEtaleBaseChange i).obj V)
          ((pointSmallEtaleBaseChangeFiberIso i s).hom.app V x)
          ((smallEtaleInverseImage.{u, v} i).obj F).obj := by
  rw [← smallEtaleInverseImageStalkIso_hom_germ_unit.{v, u} i s F V x]
  exact comp_comp_hom_inv _ _ ((smallEtaleInverseImageStalkIso.{v, u} i s).app F)

/-- The action of the fibre functor of a geometric point on morphisms is composition. -/
theorem pointSmallEtale_fiber_map_left {T : Scheme.{u}} (t : Spec (.of Ω) ⟶ T) {W W' : T.Etale}
    (φ : W ⟶ W') (w : (pointSmallEtale t).fiber.obj W) :
    ((pointSmallEtale t).fiber.map φ w).left = w.left ≫ φ.left :=
  rfl

/-- The lift of `s` to `V ×_X Z` matching a lift `x` of `s ≫ i` to `V`: its first projection. -/
@[reassoc]
theorem pointSmallEtaleBaseChangeFiberIso_hom_app_left_fst (V : X.Etale)
    (x : (pointSmallEtale (s ≫ i)).fiber.obj V) :
    ((pointSmallEtaleBaseChangeFiberIso i s).hom.app V x).left ≫ pullback.fst V.hom i = x.left := by
  simp only [pointSmallEtaleBaseChangeFiberIso, Over.mapPullbackAdj, NatIso.ofComponents_hom_app,
    Equiv.toIso_hom_hom_apply, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

/-- The lift of `s` to `V ×_X Z` matching a lift `x` of `s ≫ i` to `V`: its second projection. -/
@[reassoc]
theorem pointSmallEtaleBaseChangeFiberIso_hom_app_left_snd (V : X.Etale)
    (x : (pointSmallEtale (s ≫ i)).fiber.obj V) :
    ((pointSmallEtaleBaseChangeFiberIso i s).hom.app V x).left ≫ pullback.snd V.hom i = s := by
  simp only [pointSmallEtaleBaseChangeFiberIso, Over.mapPullbackAdj, NatIso.ofComponents_hom_app,
    Equiv.toIso_hom_hom_apply, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_snd _ _ _

/-- The lift of a geometric point to an iterated base change, transported to the base change along
the composite, is the lift along the composite. -/
theorem pointSmallEtaleBaseChangeFiberIso_comp {T T' T'' : Scheme.{u}} (g : T ⟶ T') (h : T' ⟶ T'')
    (t : Spec (.of Ω) ⟶ T) (V : T''.Etale) (x : (pointSmallEtale ((t ≫ g) ≫ h)).fiber.obj V) :
    (pointSmallEtale t).fiber.map ((smallEtaleBaseChangeComp g h).inv.app V)
        ((pointSmallEtaleBaseChangeFiberIso g t).hom.app _
          ((pointSmallEtaleBaseChangeFiberIso h (t ≫ g)).hom.app V x)) =
      (pointSmallEtaleBaseChangeFiberIso (g ≫ h) t).hom.app V
        (CategoryTheory.Over.homMk x.left (by
          rw [← Category.assoc]; exact CategoryTheory.Over.w x)) := by
  let x' : (pointSmallEtale (t ≫ g ≫ h)).fiber.obj V :=
    CategoryTheory.Over.homMk x.left (by rw [← Category.assoc]; exact CategoryTheory.Over.w x)
  have e3f := pointSmallEtaleBaseChangeFiberIso_hom_app_left_fst (g ≫ h) t V x'
  have e3s := pointSmallEtaleBaseChangeFiberIso_hom_app_left_snd (g ≫ h) t V x'
  apply CategoryTheory.Over.OverMorphism.ext
  rw [pointSmallEtale_fiber_map_left]
  apply pullback.hom_ext
  · have hhom : ((smallEtaleBaseChangeComp g h).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom h) g ≫ pullback.fst V.hom h =
          pullback.fst V.hom (g ≫ h) := by
      have {A B : Scheme.{u}} (k : A ⟶ B) :
          MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) k :=
        ⟨fun _ _ ↦ inferInstance⟩
      have {A B : Scheme.{u}} (k : A ⟶ B) : MorphismProperty.IsStableUnderBaseChangeAlong
          (@Etale : MorphismProperty Scheme.{u}) k :=
        ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
      exact MorphismProperty.Over.pullbackComp_left_fst_fst
        (P := (@Etale : MorphismProperty Scheme.{u})) (Q := ⊤) g h V
    have hi : ((smallEtaleBaseChangeComp g h).inv.app V).left ≫
        ((smallEtaleBaseChangeComp g h).hom.app V).left = 𝟙 _ :=
      congrArg (fun m => m.left) ((smallEtaleBaseChangeComp g h).inv_hom_id_app V)
    have key : ((smallEtaleBaseChangeComp g h).inv.app V).left ≫ pullback.fst V.hom (g ≫ h) =
        pullback.fst (pullback.snd V.hom h) g ≫ pullback.fst V.hom h := by
      rw [← hhom, ← Category.assoc, hi, Category.id_comp]
      rfl
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) key).trans ?_)
    have e1 := pointSmallEtaleBaseChangeFiberIso_hom_app_left_fst_assoc g t
      ((Stacks.EtaleCohomology.smallEtaleBaseChange h).obj V)
      ((pointSmallEtaleBaseChangeFiberIso h (t ≫ g)).hom.app V x) (pullback.fst V.hom h)
    have e2 := pointSmallEtaleBaseChangeFiberIso_hom_app_left_fst h (t ≫ g) V x
    exact e1.trans (e2.trans e3f.symm)
  · have key : ((smallEtaleBaseChangeComp g h).inv.app V).left ≫ pullback.snd V.hom (g ≫ h) =
        pullback.snd (pullback.snd V.hom h) g :=
      MorphismProperty.Over.w ((smallEtaleBaseChangeComp g h).inv.app V)
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) key).trans ?_)
    have e1 := pointSmallEtaleBaseChangeFiberIso_hom_app_left_snd g t
      ((Stacks.EtaleCohomology.smallEtaleBaseChange h).obj V)
      ((pointSmallEtaleBaseChangeFiberIso h (t ≫ g)).hom.app V x)
    exact e1.trans e3s.symm

private theorem comp_chain₆ {𝒞 : Type*} [Category* 𝒞] {a b c d e f k l m n : 𝒞}
    (G0 : a ⟶ b) (Ih : b ⟶ c) (Ig : c ⟶ d) (M : d ⟶ e) (Igh : e ⟶ f) (Uh : a ⟶ k) (G1 : k ⟶ c)
    (Ug : k ⟶ l) (G2 : l ⟶ d) (Cp : l ⟶ m) (G3 : m ⟶ e) (Ugh : a ⟶ n) (Mp : n ⟶ m) (G4 : n ⟶ e)
    (T : a ⟶ f) (hA : G0 ≫ Ih = Uh ≫ G1) (hB : G1 ≫ Ig = Ug ≫ G2) (hC : G2 ≫ M = Cp ≫ G3)
    (hD : Uh ≫ Ug ≫ Cp = Ugh ≫ Mp) (hE : Mp ≫ G3 = G4) (hF : Ugh ≫ G4 ≫ Igh = T) :
    G0 ≫ Ih ≫ Ig ≫ M ≫ Igh = T := by
  rw [reassoc_of% hA, reassoc_of% hB, reassoc_of% hC, reassoc_of% hD, reassoc_of% hE, hF]

/-- **Stalks of inverse images are compatible with composition** (Stacks 03Q1 for a composite):
the identification `(g⁻¹ h⁻¹ F)_t ≅ (h⁻¹ F)_{t ≫ g} ≅ F_{(t ≫ g) ≫ h}` agrees, through
`g⁻¹ h⁻¹ ≅ (g ≫ h)⁻¹`, with `((g ≫ h)⁻¹ F)_t ≅ F_{t ≫ g ≫ h}`. -/
theorem smallEtaleInverseImageStalkIso_comp {T T' T'' : Scheme.{u}} (g : T ⟶ T') (h : T' ⟶ T'')
    (t : Spec (.of Ω) ⟶ T) (F : Sheaf (smallEtaleTopology T'') (Type (max (u + 1) v))) :
    (smallEtaleInverseImageStalkIso.{v, u} h (t ≫ g)).inv.app F ≫
        (smallEtaleInverseImageStalkIso.{v, u} g t).inv.app
          ((smallEtaleInverseImage.{u, v} h).obj F) ≫
        (pointSmallEtale t).sheafFiber.map ((smallEtaleInverseImageComp.{u, v} g h).hom.app F) ≫
        (smallEtaleInverseImageStalkIso.{v, u} (g ≫ h) t).hom.app F =
      eqToHom (congrArg (fun k => (pointSmallEtale k).presheafFiber.obj F.obj)
        (Category.assoc t g h)) := by
  refine (pointSmallEtale ((t ≫ g) ≫ h)).presheafFiber_hom_ext (P := F.obj) (fun V x => ?_)
  refine Eq.trans ?_ (toPresheafFiber_comp_eqToHom.{v, u} (Category.assoc t g h) V x F.obj).symm
  let BCg := Stacks.EtaleCohomology.smallEtaleBaseChange g
  let BCh := Stacks.EtaleCohomology.smallEtaleBaseChange h
  let hF := (smallEtaleInverseImage.{u, v} h).obj F
  let ghF := (smallEtaleInverseImage.{u, v} (g ≫ h)).obj F
  let y := (pointSmallEtaleBaseChangeFiberIso h (t ≫ g)).hom.app V x
  let z := (pointSmallEtaleBaseChangeFiberIso g t).hom.app (BCh.obj V) y
  let x' : (pointSmallEtale (t ≫ g ≫ h)).fiber.obj V :=
    CategoryTheory.Over.homMk x.left (by rw [← Category.assoc]; exact CategoryTheory.Over.w x)
  have hA := toPresheafFiber_smallEtaleInverseImageStalkIso_inv.{v, u} h (t ≫ g) F V x
  have hB := toPresheafFiber_smallEtaleInverseImageStalkIso_inv.{v, u} g t hF (BCh.obj V) y
  have hC := (pointSmallEtale t).toPresheafFiber_naturality
    ((smallEtaleInverseImageComp.{u, v} g h).hom.app F).hom (BCg.obj (BCh.obj V)) z
  have hD := smallEtaleInverseImageComp_unit.{v, u} g h F V
  have hE := (pointSmallEtale t).toPresheafFiber_w ((smallEtaleBaseChangeComp g h).inv.app V) z
    ghF.obj
  rw [pointSmallEtaleBaseChangeFiberIso_comp] at hE
  have hF' := smallEtaleInverseImageStalkIso_hom_germ_unit.{v, u} (g ≫ h) t F V x'
  exact comp_chain₆ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC hD hE hF'

/-- The fibre of a geometric point at an étale scheme isomorphic to the base has one element. -/
theorem subsingleton_pointSmallEtale_fiber_obj_of_isIso {T : Scheme.{u}} {Ω' : Type u} [Field Ω']
    [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ T) (W : T.Etale) [IsIso W.hom] :
    Subsingleton ((pointSmallEtale t).fiber.obj W) :=
  ⟨fun a b => CategoryTheory.Over.OverMorphism.ext <|
    (cancel_mono W.hom).1 ((CategoryTheory.Over.w a).trans (CategoryTheory.Over.w b).symm)⟩

/-- The fibre of a geometric point at a final object of the small étale site has one element. -/
theorem subsingleton_pointSmallEtale_fiber_obj_of_isTerminal {T : Scheme.{u}} {Ω' : Type u}
    [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ T) {W : T.Etale} (hW : IsTerminal W) :
    Subsingleton ((pointSmallEtale t).fiber.obj W) := by
  have : IsIso (Scheme.Etale.mk (𝟙 T)).hom := inferInstanceAs (IsIso (𝟙 T))
  have := subsingleton_pointSmallEtale_fiber_obj_of_isIso t (Scheme.Etale.mk (𝟙 T))
  let e := hW.uniqueUpToIso (isTerminalEtaleMkId T)
  refine ⟨fun a b => ?_⟩
  have h : ∀ c, (pointSmallEtale t).fiber.map e.inv ((pointSmallEtale t).fiber.map e.hom c) = c :=
    fun c => by
      rw [← Functor.map_comp_apply, e.hom_inv_id, Functor.map_id_apply]
  rw [← h a, ← h b, Subsingleton.elim ((pointSmallEtale t).fiber.map e.hom a)]

/-- Bookkeeping for `smallEtaleGlobalSectionsComparison_sheafFiberClosedPointIsoGamma_inv`, in an
arbitrary category (so that the instantiation is checked syntactically). -/
private theorem comp_germ_chain {𝒞 : Type*} [Category* 𝒞] {A B B' C D E E' H K : 𝒞}
    (ΓX : A ⟶ B) (U : B ⟶ B') (Mg : B' ⟶ C) (Zi : C ⟶ D) (Ze : D ⟶ E) (germ : E ⟶ H)
    (I : H ⟶ K) (Mh : C ⟶ E) (germW : B' ⟶ H) (Mf : B ⟶ E') (germXe : E' ⟶ K) (germX : B ⟶ K)
    (hZ : Zi ≫ Ze = Mh) (hw : Mg ≫ Mh ≫ germ = germW) (hmain : U ≫ germW ≫ I = germX)
    (hwX : Mf ≫ germXe = germX) :
    ΓX ≫ (U ≫ Mg) ≫ Zi ≫ (Ze ≫ germ) ≫ I = (ΓX ≫ Mf) ≫ germXe := by
  rw [Category.assoc ΓX Mf, hwX, ← hmain, ← hw, ← hZ]
  simp only [Category.assoc]

section ClosedPoint

variable {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R] {R' : Type u} [CommRing R']
  [StrictlyHenselianLocalRing R'] {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']

/-- **Germs at a closed point of the pull-back of a global section** (Stacks 03Q1 at the closed
points of strictly henselian local schemes): for `i : Spec R' ⟶ Spec R` and a closed geometric
point `y` of `Spec R'` with `y ≫ i` closed, the germ at `y` of the pull-back `i^* σ` of a global
section `σ` corresponds, under `(i⁻¹ G)_y ≅ G_{y ≫ i}`, to the germ of `σ` at `y ≫ i`. -/
theorem smallEtaleGlobalSectionsComparison_sheafFiberClosedPointIsoGamma_inv
    (i : Spec (.of R') ⟶ Spec (.of R)) (y : Spec (.of Ω') ⟶ Spec (.of R'))
    (hy : y (default : Spec (.of Ω')) = IsLocalRing.closedPoint R')
    (hyi : (y ≫ i) (default : Spec (.of Ω')) = IsLocalRing.closedPoint R)
    (G : Sheaf (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v))) :
    (smallEtaleGlobalSectionsComparison.{u, v} i).app G ≫
        (sheafFiberClosedPointIsoGamma.{u, v} y hy).inv.app
          ((smallEtaleInverseImage.{u, v} i).obj G) ≫
        (smallEtaleInverseImageStalkIso.{v, u} i y).hom.app G =
      (sheafFiberClosedPointIsoGamma.{u, v} (y ≫ i) hyi).inv.app G := by
  let BC := Stacks.EtaleCohomology.smallEtaleBaseChange i
  let tX := terminal (Spec (.of R)).Etale
  let tZ := terminal (Spec (.of R')).Etale
  let eX := Scheme.Etale.mk (𝟙 (Spec (.of R)))
  let eZ := Scheme.Etale.mk (𝟙 (Spec (.of R')))
  let f : eX ⟶ tX := terminal.from eX
  let h : eZ ⟶ tZ := terminal.from eZ
  let g : tZ ⟶ BC.obj tX := (isTerminalSmallEtaleBaseChangeObjTerminal i).from _
  let ptX := pointSmallEtaleClosedPointElement (y ≫ i)
  let ptZ := pointSmallEtaleClosedPointElement y
  let x := (pointSmallEtale (y ≫ i)).fiber.map f ptX
  let iG := (smallEtaleInverseImage.{u, v} i).obj G
  have hpt : (pointSmallEtale y).fiber.map (h ≫ g) ptZ =
      (pointSmallEtaleBaseChangeFiberIso i y).hom.app tX x :=
    (subsingleton_pointSmallEtale_fiber_obj_of_isTerminal y
      (isTerminalSmallEtaleBaseChangeObjTerminal i)).elim _ _
  have hR : (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R)))
      (Type (max (u + 1) v)) (isTerminalEtaleMkId (Spec (.of R)))).hom.app G =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R)))
        (Type (max (u + 1) v)) terminalIsTerminal).hom.app G ≫ G.obj.map f.op := by
    rw [Sheaf.ΓNatIsoSheafSections_hom_app_general, Sheaf.ΓNatIsoSheafSections_hom_app_general,
      Sheaf.ΓRes_map]
  have hZ : (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R')))
      (Type (max (u + 1) v)) terminalIsTerminal).inv.app iG ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R')))
        (Type (max (u + 1) v)) (isTerminalEtaleMkId (Spec (.of R')))).hom.app iG =
      iG.obj.map h.op := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, Sheaf.ΓNatIsoSheafSections_hom_app_general,
      Sheaf.ΓNatIsoSheafSections_hom_app_general, Sheaf.ΓRes_map]
  have hw : iG.obj.map g.op ≫ iG.obj.map h.op ≫
      (pointSmallEtale y).toPresheafFiber eZ ptZ iG.obj =
      (pointSmallEtale y).toPresheafFiber (BC.obj tX)
        ((pointSmallEtaleBaseChangeFiberIso i y).hom.app tX x) iG.obj := by
    rw [← hpt, ← (pointSmallEtale y).toPresheafFiber_w (h ≫ g), op_comp, Functor.map_comp,
      Category.assoc]
  have hwX : G.obj.map f.op ≫ (pointSmallEtale (y ≫ i)).toPresheafFiber eX ptX G.obj =
      (pointSmallEtale (y ≫ i)).toPresheafFiber tX x G.obj :=
    (pointSmallEtale (y ≫ i)).toPresheafFiber_w f ptX G.obj
  have hmain := smallEtaleInverseImageStalkIso_hom_germ_unit.{v, u} i y G tX x
  simp only [smallEtaleGlobalSectionsComparison, Stacks.Sites.globalSectionsPullbackComparison_app,
    Stacks.Sites.sectionsPullbackComparison_app, sheafFiberClosedPointIsoGamma,
    presheafFiberClosedPointIsoSections, Category.assoc]
  change (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v))
      terminalIsTerminal).hom.app G ≫
    (((smallEtaleInverseImageAdjunction.{u, v} i).unit.app G).hom.app (op tX) ≫ iG.obj.map g.op) ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R'))) (Type (max (u + 1) v))
        terminalIsTerminal).inv.app iG ≫
      ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R'))) (Type (max (u + 1) v))
        (isTerminalEtaleMkId (Spec (.of R')))).hom.app iG ≫
        (pointSmallEtale y).toPresheafFiber eZ ptZ iG.obj) ≫
      (smallEtaleInverseImageStalkIso.{v, u} i y).hom.app G =
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v))
        (isTerminalEtaleMkId (Spec (.of R)))).hom.app G ≫
      (pointSmallEtale (y ≫ i)).toPresheafFiber eX ptX G.obj
  rw [hR]
  exact comp_germ_chain _ _ _ _ _ _ _ _ _ _ _ _ hZ hw hmain hwX

/-- Changing the source of a morphism of geometric points along an equality of geometric points. -/
theorem pointSmallEtaleHom_sheafFiber_app_comp_eqToHom {T : Scheme.{u}} {t₁ t₂ : Spec (.of Ω') ⟶ T}
    (e : t₁ = t₂) (t' : Spec (.of Ω') ⟶ T) (a : Spec (.of Ω') ⟶ Spec (.of Ω')) (ha : a ≫ t' = t₁)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    (pointSmallEtaleHom t₁ t' a ha).sheafFiber.app F ≫
        eqToHom (congrArg (fun k => (pointSmallEtale k).presheafFiber.obj F.obj) e) =
      (pointSmallEtaleHom t₂ t' a (ha.trans e)).sheafFiber.app F := by
  subst e
  exact Category.comp_id _

private theorem theta_chain {𝒞 : Type*} [Category* 𝒞] {a b c d e f g' k : 𝒞}
    (Iπ : b ≅ a) (Cyb : b ≅ c) (Comp : c ⟶ d) (Gm : d ⟶ e) (Cy : f ≅ d) (Ib : f ≅ b)
    (Fm : f ⟶ g') (Cy' : g' ≅ e) (Ibp : g' ≅ k) (eq : a ⟶ k)
    (hG : Comp ≫ Cy.inv ≫ Ib.hom = Cyb.inv) (hN : Cy.hom ≫ Gm = Fm ≫ Cy'.hom)
    (hC : Iπ.inv ≫ Ib.inv ≫ Fm ≫ Ibp.hom = eq) :
    (Iπ.inv ≫ Cyb.hom) ≫ Comp ≫ Gm = eq ≫ (Ibp.inv ≫ Cy'.hom) := by
  have h1 : Cyb.hom ≫ Comp = Ib.inv ≫ Cy.hom := by
    rw [← cancel_mono Cy.inv, ← cancel_mono Ib.hom]
    simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id, Category.comp_id]
    rw [hG, Iso.hom_inv_id]
  rw [← hC, Category.assoc, reassoc_of% h1, hN]
  simp

variable {S : Scheme.{u}}

/-- **The closed-point identification of stalks along a composite** `Spec R' ⟶ Spec R ⟶ S`: for
a closed geometric point `y` of `Spec R'` with `y ≫ β` closed, `Θ_{y ≫ β}` for `π` followed by
pull-back of global sections along `β` is `Θ_y` for `β ≫ π`. -/
theorem closedPointStalkIsoGamma_hom_app_comp (π : Spec (.of R) ⟶ S)
    (β : Spec (.of R') ⟶ Spec (.of R)) (y : Spec (.of Ω') ⟶ Spec (.of R'))
    (hy : y (default : Spec (.of Ω')) = IsLocalRing.closedPoint R')
    (hyβ : (y ≫ β) (default : Spec (.of Ω')) = IsLocalRing.closedPoint R)
    (F : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) :
    (closedPointStalkIsoGamma.{u, v} π (y ≫ β) hyβ).hom.app F ≫
        (smallEtaleGlobalSectionsComparison.{u, v} β).app
          ((smallEtaleInverseImage.{u, v} π).obj F) ≫
        (Sheaf.Γ (smallEtaleTopology (Spec (.of R'))) (Type (max (u + 1) v))).map
          ((smallEtaleInverseImageComp.{u, v} β π).hom.app F) =
      eqToHom (congrArg (fun k => (pointSmallEtale k).presheafFiber.obj F.obj)
          (Category.assoc y β π)) ≫
        (closedPointStalkIsoGamma.{u, v} (β ≫ π) y hy).hom.app F := by
  let H := (smallEtaleInverseImage.{u, v} π).obj F
  have hG :=
    smallEtaleGlobalSectionsComparison_sheafFiberClosedPointIsoGamma_inv.{v, u} β y hy hyβ H
  have hN := ((sheafFiberClosedPointIsoGamma.{u, v} y hy).hom.naturality
    ((smallEtaleInverseImageComp.{u, v} β π).hom.app F)).symm
  have hC := smallEtaleInverseImageStalkIso_comp.{v, u} β π y F
  exact theta_chain ((smallEtaleInverseImageStalkIso.{v, u} π (y ≫ β)).app F)
    ((sheafFiberClosedPointIsoGamma.{u, v} (y ≫ β) hyβ).app H) _ _
    ((sheafFiberClosedPointIsoGamma.{u, v} y hy).app ((smallEtaleInverseImage.{u, v} β).obj H))
    ((smallEtaleInverseImageStalkIso.{v, u} β y).app H) _
    ((sheafFiberClosedPointIsoGamma.{u, v} y hy).app
      ((smallEtaleInverseImage.{u, v} (β ≫ π)).obj F))
    ((smallEtaleInverseImageStalkIso.{v, u} (β ≫ π) y).app F) _ hG hN hC

/-- **The Frobenius on a stalk is pull-back of sections along an endomorphism of the strict
henselization** (step F3 of the Frobenius equivariance of `H⁰_loc`, Weil II 1.8): let `y'` be a
closed geometric point of `Spec R` over `S` and `β : Spec R' ⟶ Spec R` with a closed geometric
point `y` of `Spec R'` and `a ≫ y' = y ≫ β`. Through `Θ_{y'} : F_{y' ≫ π} ≅ Γ(Spec R, π⁻¹ F)` and
`Θ_y : F_{y ≫ β ≫ π} ≅ Γ(Spec R', (β ≫ π)⁻¹ F)`, pull-back of global sections along `β` is the map
of stalks induced by `a`. For `R' = R`, `β` the endomorphism of the strict henselization lifting
a Frobenius `a` and `β ≫ π = π`, this is the Frobenius on the stalk. -/
theorem closedPointStalkIsoGamma_hom_app_pullback (π : Spec (.of R) ⟶ S)
    (β : Spec (.of R') ⟶ Spec (.of R)) (y : Spec (.of Ω') ⟶ Spec (.of R'))
    (y' : Spec (.of Ω') ⟶ Spec (.of R))
    (hy : y (default : Spec (.of Ω')) = IsLocalRing.closedPoint R')
    (hy' : y' (default : Spec (.of Ω')) = IsLocalRing.closedPoint R)
    (a : Spec (.of Ω') ⟶ Spec (.of Ω')) (ha : a ≫ y' = y ≫ β)
    (F : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) :
    (closedPointStalkIsoGamma.{u, v} π y' hy').hom.app F ≫
        (smallEtaleGlobalSectionsComparison.{u, v} β).app
          ((smallEtaleInverseImage.{u, v} π).obj F) ≫
        (Sheaf.Γ (smallEtaleTopology (Spec (.of R'))) (Type (max (u + 1) v))).map
          ((smallEtaleInverseImageComp.{u, v} β π).hom.app F) =
      (pointSmallEtaleHom (y ≫ β ≫ π) (y' ≫ π) a (by
          rw [← Category.assoc, ha, Category.assoc])).sheafFiber.app F ≫
        (closedPointStalkIsoGamma.{u, v} (β ≫ π) y hy).hom.app F := by
  have hyβ : (y ≫ β) (default : Spec (.of Ω')) = IsLocalRing.closedPoint R := by
    rw [← ha, Scheme.Hom.comp_apply, Subsingleton.elim (a (default : Spec (.of Ω'))) default, hy']
  have h3a := NatTrans.congr_app
    (pointSmallEtaleHom_sheafFiber_closedPointStalkIsoGamma_hom.{u, v} π (y ≫ β) y' hyβ hy' a ha) F
  simp only [NatTrans.comp_app] at h3a
  rw [← h3a, Category.assoc, closedPointStalkIsoGamma_hom_app_comp.{v, u} π β y hy hyβ F]
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ (closedPointStalkIsoGamma.{u, v} (β ≫ π) y hy).hom.app F)
    (pointSmallEtaleHom_sheafFiber_app_comp_eqToHom.{v, u} (Category.assoc y β π) (y' ≫ π) a _ F)

/-- Moving both geometric points of a morphism of points along equalities of geometric points. -/
theorem pointSmallEtaleHom_sheafFiber_app_eqToHom {T : Scheme.{u}}
    {t₁ t₂ t₁' t₂' : Spec (.of Ω') ⟶ T}
    (e : t₁ = t₂) (e' : t₁' = t₂') (a : Spec (.of Ω') ⟶ Spec (.of Ω')) (ha : a ≫ t₁' = t₁)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    (pointSmallEtaleHom t₁ t₁' a ha).sheafFiber.app F =
      eqToHom (congrArg (fun k => (pointSmallEtale k).presheafFiber.obj F.obj) e') ≫
        (pointSmallEtaleHom t₂ t₂' a (by rw [← e, ← e', ha])).sheafFiber.app F ≫
        eqToHom (congrArg (fun k => (pointSmallEtale k).presheafFiber.obj F.obj) e.symm) := by
  subst e e'
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The closed-point identification `Θ_y` along an equality of morphisms `π = π'`. -/
theorem closedPointStalkIsoGamma_hom_app_eqToHom {π π' : Spec (.of R) ⟶ S} (e : π = π')
    (y : Spec (.of Ω') ⟶ Spec (.of R))
    (hy : y (default : Spec (.of Ω')) = IsLocalRing.closedPoint R)
    (F : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) :
    (closedPointStalkIsoGamma.{u, v} π y hy).hom.app F ≫
        (Sheaf.Γ (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v))).map
          (eqToHom (congrArg (fun k => (smallEtaleInverseImage.{u, v} k).obj F) e)) =
      eqToHom (congrArg (fun k => (pointSmallEtale (y ≫ k)).presheafFiber.obj F.obj) e) ≫
        (closedPointStalkIsoGamma.{u, v} π' y hy).hom.app F := by
  subst e
  exact (congrArg ((closedPointStalkIsoGamma.{u, v} π y hy).hom.app F ≫ ·)
    ((Sheaf.Γ (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v))).map_id
      ((smallEtaleInverseImage.{u, v} π).obj F))).trans
    ((Category.comp_id _).trans (Category.id_comp _).symm)

end ClosedPoint

section StrictHenselization

private theorem frobenius_chain {𝒞 : Type*} [Category* 𝒞] {a b c d e f : 𝒞} (E0 : a ⟶ b)
    (HP : b ⟶ c) (E1 : c ⟶ a) (Θ : b ⟶ d) (Cm : d ⟶ e) (Gc : e ⟶ f) (GE : f ⟶ d) (Θβ : c ⟶ f)
    (E2 : c ⟶ b) (h12 : E1 ≫ E0 = E2) (hF3 : Θ ≫ Cm ≫ Gc = HP ≫ Θβ)
    (hEq : Θβ ≫ GE = E2 ≫ Θ) :
    (E0 ≫ HP ≫ E1) ≫ (E0 ≫ Θ) = (E0 ≫ Θ) ≫ (Cm ≫ Gc ≫ GE) := by
  simp only [Category.assoc]
  rw [reassoc_of% hF3, hEq, reassoc_of% h12]

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {s : GeometricPoint S}
  (a : GeometricPoint.Hom s s)

/-- **The Frobenius on sections over the strict henselization**: for an endomorphism `a` of the
geometric point `s` (a lift of a Frobenius), pull-back of sections of `π⁻¹ G` over
`Spec 𝒪^{sh}_{S,s}` along the induced endomorphism `β_a` of the strict henselization, followed by
`β_a⁻¹ π⁻¹ ≅ (β_a ≫ π)⁻¹ = π⁻¹`. -/
def strictHenselizationSectionsPullback :
    smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B S hS s) ⋙
        Sheaf.Γ (strictHenselization B S hS s).smallEtaleTopology (Type (u + 1)) ⟶
      smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B S hS s) ⋙
        Sheaf.Γ (strictHenselization B S hS s).smallEtaleTopology (Type (u + 1)) :=
  Functor.whiskerLeft _ (smallEtaleGlobalSectionsComparison.{u, 0}
      (strictHenselizationEndomorphism B S hS a)) ≫
    Functor.whiskerRight
      ((smallEtaleInverseImageComp.{u, 0} (strictHenselizationEndomorphism B S hS a)
          (strictHenselizationToBase B S hS s)).hom ≫
        eqToHom (congrArg (fun k => smallEtaleInverseImage.{u, 0} k)
          (strictHenselizationEndomorphism_comp_toBase B S hS a))) _

/-- **Frobenius equivariance of the stalk as sections over the strict henselization** (step F3 of
`H⁰_loc`, Weil II 1.8): the identification `F_s ≅ Γ(Spec 𝒪^{sh}_{S,s}, π⁻¹ F)` carries the map of
stalks induced by an endomorphism `a` of `s` (Tag 04FN) to pull-back of sections along the
induced endomorphism `β_a` of the strict henselization. -/
theorem smallEtalePointHom_sheafFiber_comp_stalkIsoStrictHenselizationGamma_hom :
    (smallEtalePointHom S a).sheafFiber ≫ (stalkIsoStrictHenselizationGamma B S hS s).hom =
      (stalkIsoStrictHenselizationGamma B S hS s).hom ≫
        strictHenselizationSectionsPullback B S hS a := by
  refine NatTrans.ext (funext fun G => ?_)
  let π := strictHenselizationToBase B S hS s
  let pt := geometricPointToStrictHenselization B S hS s
  let β := strictHenselizationEndomorphism B S hS a
  have hpt := geometricPointToStrictHenselization_base_default B S hS s
  have ha : a.hom ≫ pt = pt ≫ β :=
    (geometricPointToStrictHenselization_comp_strictHenselizationEndomorphism B S hS a).symm
  have hβ : β ≫ π = π := strictHenselizationEndomorphism_comp_toBase B S hS a
  have e0 : s.hom = pt ≫ π := (geometricPointToStrictHenselization_comp B S hS s).symm
  have hF3 := closedPointStalkIsoGamma_hom_app_pullback.{0, u} π β pt pt hpt hpt a.hom ha G
  have hEq := closedPointStalkIsoGamma_hom_app_eqToHom.{0, u} hβ pt hpt G
  have hH := pointSmallEtaleHom_sheafFiber_app_eqToHom.{0, u} (e0.trans (by rw [hβ]) :
    s.hom = pt ≫ β ≫ π) e0 a.hom a.comm G
  have hSt : (stalkIsoStrictHenselizationGamma B S hS s).hom.app G =
      eqToHom (congrArg (fun k => (pointSmallEtale k).presheafFiber.obj G.obj) e0) ≫
        (closedPointStalkIsoGamma.{u, 0} π pt hpt).hom.app G := by
    simp only [stalkIsoStrictHenselizationGamma, closedPointStalkIsoGamma, Iso.trans_hom,
      NatTrans.comp_app, eqToIso.hom, eqToHom_app]
    rfl
  have hHom : (smallEtalePointHom S a).sheafFiber.app G =
      (pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app G := rfl
  rw [NatTrans.comp_app, NatTrans.comp_app, hSt, hHom, hH]
  simp only [strictHenselizationSectionsPullback, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, eqToHom_app]
  exact frobenius_chain _ _ _ _ _ _ _ _ _ (eqToHom_trans _ _) hF3 hEq

end StrictHenselization

end AlgebraicGeometry

end
