module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemExistence
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroFunctor

/-!
# Extension by zero along an open immersion of Noetherian schemes

Let `j : U ⟶ X` be an open immersion of Noetherian schemes. The Deligne-system assignment
`AlgebraicGeometry.DeligneSystem.values` of Stacks 0G4L (2) and Stacks 0G2H determines the
extension by zero

`Rj_! : D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_X)`

of Stacks 0G4N, whose functor of points at `K` is `L ↦ Hom_U(K, L|_U)`. Since that functor of
points does not depend on the Deligne system chosen for `K`, `Rj_! K` is identified with the
pro-object of *every* Deligne system with value `K`, through the restriction map of Stacks 0G2H;
this is what lets one compute `Rj_!` on a particular Deligne system, such as the system
`(𝓘^n 𝓕^•)` of a chosen complex `𝓕^•` and ideal `𝓘`.

Stacks 0G4N says moreover that `Rj_!` is "left adjoint" to `j^*` by Stacks 0G2H and "exact" by
Stacks 0G4M. The adjointness is the natural bijection `Hom_{Pro}(Rj_! K, L) = Hom_U(K, L|_U)`
for `L` in `D^b_{Coh}(𝒪_X)` viewed as a constant pro-object. The exactness says that a
distinguished triangle `K ⟶ L ⟶ M ⟶ K[1]` of `D^b_{Coh}(𝒪_U)` is sent to the pro-system of the
inverse system of distinguished triangles `K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]` of Stacks 0G4M. Both rest on
the comparison map `Rj_! K ⟶ (F_n)` attached to an inverse system `(F_n)` of `D^b_{Coh}(𝒪_X)` and
an identification `e` of `(F_n|_U)` with the constant system at `K`: on functors of points it
sends the class of `f : F_n ⟶ N` to `e_n⁻¹ ≫ f|_U`, it is an isomorphism when Stacks 0G2H holds
for `(F_n)`, and it is natural in `(F_n, e)`. It is defined for any functor `j^*`, as
`CategoryTheory.extensionByZeroComparison`, because the exactness needs it for the shifted
system `(K_n[1])` as well as for the three vertex systems.

## Main definitions

* `CategoryTheory.extensionByZeroComparison`: the comparison map `Rj_! K ⟶ (F_n)`.
* `AlgebraicGeometry.extensionByZeroOpenImmersion`: the functor `Rj_!`.
* `AlgebraicGeometry.DeligneSystem.valueOfIso`: a Deligne system together with an identification
  of its restriction with a constant system, packaged with Stacks 0G2H as a
  `AlgebraicGeometry.DeligneSystem.Value`.
* `AlgebraicGeometry.DeligneSystem.ofComplexValue`: the value of the system `(𝓘^n 𝓕^•)`, given
  an identification of `𝓕^•|_U` with an object of `D^b_{Coh}(𝒪_U)`.
* `AlgebraicGeometry.DeligneSystem.Value.extensionByZeroIso`: `Rj_! K` is the pro-object of any
  Deligne system with value `K`.

## Main results

* `CategoryTheory.extensionByZero_map_comp_comparison`: naturality of the comparison map.
* `AlgebraicGeometry.extensionByZeroOpenImmersionHomIso`: `Rj_!` is "left adjoint" to `j^*`,
  [Stacks, Tag 0G4N].
* `AlgebraicGeometry.extensionByZeroOpenImmersion_exact`: `Rj_!` is "exact", [Stacks, Tag 0G4N].
* `AlgebraicGeometry.DeligneSystem.Value.pointsIso_inv_app_ι`: the identification of functors of
  points underlying `extensionByZeroIso` is the restriction map.
* `AlgebraicGeometry.DeligneSystem.ofComplex_restrictIsoConst_hom_app`: for the system
  `(𝓘^n 𝓕^•)`, the identification of the restricted system with the constant system at `𝓕^•|_U`
  is the restriction of the inclusions `𝓘^n 𝓕^• ⟶ 𝓕^•`.

## References

* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 0G4M](https://stacks.math.columbia.edu/tag/0G4M)
* [Stacks Project, Tag 0G4L](https://stacks.math.columbia.edu/tag/0G4L)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance 10000] HasDerivedCategory.standard

universe v u u'

namespace CategoryTheory

section Comparison

variable {𝒞 : Type u'} [Category.{v} 𝒞] {𝒟 : Type u} [Category.{v} 𝒟] (jstar : 𝒟 ⥤ 𝒞)

/-- The transformation `colim_n Mor_𝒟(F_n, -) ⟶ Mor_𝒞(K, j^* -)` attached to an identification
`e` of `F ⋙ j^*` with the constant system at `K`: the class of `f : F_n ⟶ N` is sent to
`e_n⁻¹ ≫ j^* f`. -/
public def restrictionPointsHom {F : ℕᵒᵖ ⥤ 𝒟} {K : 𝒞}
    (e : F ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj K) :
    Pro.coyonedaColim (Pro.liftedInverseSequence F) ⟶ jstar ⋙ coyoneda.obj (op K) :=
  (Pro.seqHomColimIso F).hom ≫ proHomComparison F jstar (coneOfNatIso e ⟨K, 𝟙 _⟩)

/-- `CategoryTheory.restrictionPointsHom` sends the class of `f : F_n ⟶ N` to `e_n⁻¹ ≫ j^* f`. -/
public lemma restrictionPointsHom_app_ι {F : ℕᵒᵖ ⥤ 𝒟} {K : 𝒞}
    (e : F ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj K) (i : (ULiftHom.{v} (ULift.{v} ℕᵒᵖ))ᵒᵖ) (N : 𝒟)
    (f : (Pro.liftedInverseSequence F).obj i.unop ⟶ N) :
    (restrictionPointsHom jstar e).app N
        ((colimit.ι ((Pro.liftedInverseSequence F).op ⋙ coyoneda) i).app N f) =
      e.inv.app (Pro.liftedIndexDown i) ≫ jstar.map f := by
  have h : colimit.ι ((Pro.liftedInverseSequence F).op ⋙ coyoneda) i ≫
      (Pro.seqHomColimIso F).hom =
        colimit.ι (F.op ⋙ coyoneda) (op (op (Pro.liftedIndexDown i).unop)) := by
    refine (HasColimit.ι_isoOfEquivalence_hom (F := (Pro.liftedInverseSequence F).op ⋙ coyoneda)
      (G := F.op ⋙ coyoneda) (ULiftHomULiftCategory.equiv ℕᵒᵖ).symm.op (Iso.refl _) i).trans ?_
    exact Category.id_comp _
  have h₂ : (restrictionPointsHom jstar e).app N
      ((colimit.ι ((Pro.liftedInverseSequence F).op ⋙ coyoneda) i).app N f) =
        (proHomComparison F jstar (coneOfNatIso e ⟨K, 𝟙 _⟩)).app N
          (Pro.seqStage F (n := (Pro.liftedIndexDown i).unop) f) := by
    rw [Pro.seqStage, ← h]
    rfl
  rw [h₂, proHomComparison_stage]
  simp [coneOfNatIso]

variable (A : DeligneSystemAssignment jstar)

/-- **The comparison map `Rj_! K ⟶ (F_n)`** attached to an inverse sequence `F` in `𝒟` and an
identification `e` of `F ⋙ j^*` with the constant system at `K`. On functors of points it is
`CategoryTheory.restrictionPointsHom`: the class of `f : F_n ⟶ N` goes to `e_n⁻¹ ≫ j^* f`. -/
public def extensionByZeroComparison {F : ℕᵒᵖ ⥤ 𝒟} {K : 𝒞}
    (e : F ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj K) :
    (extensionByZero jstar A).obj K ⟶ ProSeq.of F :=
  (ObjectProperty.homMk (X := (ProSeq.of F).unop) (Y := ((extensionByZero jstar A).obj K).unop)
    (restrictionPointsHom jstar e)).op

/-- The comparison map is an isomorphism when `j^*` identifies `colim_n Mor_𝒟(F_n, N)` with
`colim_n Mor_𝒞(j^* F_n, j^* N)` for every `N`, which for a Deligne system is Stacks 0G2H. -/
public def extensionByZeroComparisonIso {F : ℕᵒᵖ ⥤ 𝒟} {K : 𝒞}
    (e : F ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj K) (hF : ∀ N, RestrictionLifting F jstar N) :
    (extensionByZero jstar A).obj K ≅ ProSeq.of F :=
  (ObjectProperty.isoMk (X := (ProSeq.of F).unop) (Y := ((extensionByZero jstar A).obj K).unop) _
    (Pro.seqHomColimIso F ≪≫ restrictHomIso F jstar K e hF)).op

/-- The forward map of `CategoryTheory.extensionByZeroComparisonIso` is the comparison map
`CategoryTheory.extensionByZeroComparison`. -/
@[simp]
public lemma extensionByZeroComparisonIso_hom {F : ℕᵒᵖ ⥤ 𝒟} {K : 𝒞}
    (e : F ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj K) (hF : ∀ N, RestrictionLifting F jstar N) :
    (extensionByZeroComparisonIso jstar A e hF).hom = extensionByZeroComparison jstar A e :=
  rfl

/-- **Naturality of the comparison map.** A morphism `α : F ⟶ G` of inverse sequences restricting,
under the identifications with constant systems, to `φ : K ⟶ L` intertwines `Rj_! φ` with the
morphism of pro-objects induced by `α`. In particular `Rj_!` sends `φ` to the morphism of
pro-objects induced by any such `α`. -/
public lemma extensionByZero_map_comp_comparison {F G : ℕᵒᵖ ⥤ 𝒟} {K L : 𝒞}
    (eF : F ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj K) (eG : G ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj L)
    (α : F ⟶ G) (φ : K ⟶ L)
    (h : ∀ n, jstar.map (α.app n) ≫ eG.hom.app n = eF.hom.app n ≫ φ) :
    (extensionByZero jstar A).map φ ≫ extensionByZeroComparison jstar A eG =
      extensionByZeroComparison jstar A eF ≫ ProSeq.ofMap α := by
  apply Quiver.Hom.unop_inj
  ext1
  refine colimit.hom_ext fun i => ?_
  ext N g
  have hn : φ ≫ eG.inv.app (Pro.liftedIndexDown i) =
      eF.inv.app (Pro.liftedIndexDown i) ≫ jstar.map (α.app (Pro.liftedIndexDown i)) := by
    rw [← cancel_epi (eF.hom.app _), ← Category.assoc, ← h]
    simp
  show φ ≫ (restrictionPointsHom jstar eG).app N
      ((colimit.ι ((Pro.liftedInverseSequence G).op ⋙ coyoneda) i).app N g) =
    (restrictionPointsHom jstar eF).app N
      ((colimit.ι ((Pro.liftedInverseSequence G).op ⋙ coyoneda) i ≫
        (ProSeq.ofMap α).unop.hom).app N g)
  rw [ProSeq.ι_ofMap_unop_hom]
  show φ ≫ (restrictionPointsHom jstar eG).app N
      ((colimit.ι ((Pro.liftedInverseSequence G).op ⋙ coyoneda) i).app N g) =
    (restrictionPointsHom jstar eF).app N
      ((colimit.ι ((Pro.liftedInverseSequence F).op ⋙ coyoneda) i).app N
        (α.app (Pro.liftedIndexDown i) ≫ g))
  rw [restrictionPointsHom_app_ι, restrictionPointsHom_app_ι, jstar.map_comp, ← Category.assoc,
    hn, Category.assoc]

end Comparison

section Triangles

variable {𝒞 : Type u'} [Category.{v} 𝒞] [HasShift 𝒞 ℤ] {𝒟 : Type u} [Category.{v} 𝒟]
  [HasShift 𝒟 ℤ] [Preadditive 𝒞] [Preadditive 𝒟] (jstar : 𝒟 ⥤ 𝒞) [jstar.CommShift ℤ]
  {TX : ℕᵒᵖ ⥤ Triangle 𝒟} {T : Triangle 𝒞}

/-- The first vertex system of an inverse system of triangles whose restriction is constant at
`T` restricts to the constant system at the first vertex of `T`. -/
public def mapTriangleConstIsoπ₁ (e : TX ⋙ jstar.mapTriangle ≅ (Functor.const ℕᵒᵖ).obj T) :
    (TX ⋙ Triangle.π₁) ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj T.obj₁ :=
  NatIso.ofComponents (fun n => Triangle.π₁.mapIso (e.app n))
    (fun f => congrArg TriangleMorphism.hom₁ (e.hom.naturality f))

/-- The second vertex system restricts to the constant system at the second vertex of `T`. -/
public def mapTriangleConstIsoπ₂ (e : TX ⋙ jstar.mapTriangle ≅ (Functor.const ℕᵒᵖ).obj T) :
    (TX ⋙ Triangle.π₂) ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj T.obj₂ :=
  NatIso.ofComponents (fun n => Triangle.π₂.mapIso (e.app n))
    (fun f => congrArg TriangleMorphism.hom₂ (e.hom.naturality f))

/-- The third vertex system restricts to the constant system at the third vertex of `T`. -/
public def mapTriangleConstIsoπ₃ (e : TX ⋙ jstar.mapTriangle ≅ (Functor.const ℕᵒᵖ).obj T) :
    (TX ⋙ Triangle.π₃) ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj T.obj₃ :=
  NatIso.ofComponents (fun n => Triangle.π₃.mapIso (e.app n))
    (fun f => congrArg TriangleMorphism.hom₃ (e.hom.naturality f))

/-- The shifted first vertex system `(K_n[1])` restricts to the constant system at `K[1]`, through
the commutation of `j^*` with the shift. -/
public def mapTriangleConstIsoShiftπ₁
    (e : TX ⋙ jstar.mapTriangle ≅ (Functor.const ℕᵒᵖ).obj T) :
    (TX ⋙ Triangle.π₁ ⋙ shiftFunctor 𝒟 (1 : ℤ)) ⋙ jstar ≅
      (Functor.const ℕᵒᵖ).obj ((shiftFunctor 𝒞 (1 : ℤ)).obj T.obj₁) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (TX ⋙ Triangle.π₁) (jstar.commShiftIso (1 : ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapTriangleConstIsoπ₁ jstar e) (shiftFunctor 𝒞 (1 : ℤ)) ≪≫
    Functor.constComp _ _ _

variable (A : DeligneSystemAssignment jstar)
  (e : TX ⋙ jstar.mapTriangle ≅ (Functor.const ℕᵒᵖ).obj T)

omit [Preadditive 𝒞] [Preadditive 𝒟] in
/-- **`Rj_!` on the first map of a triangle**: the comparison maps for the vertex systems of an
inverse system of triangles restricting to `T` intertwine `Rj_!` of the first map of `T` with
the morphism of pro-objects induced by the first maps of the triangles. -/
public lemma extensionByZero_map_mor₁_comp_comparison :
    (extensionByZero jstar A).map T.mor₁ ≫
        extensionByZeroComparison jstar A (mapTriangleConstIsoπ₂ jstar e) =
      extensionByZeroComparison jstar A (mapTriangleConstIsoπ₁ jstar e) ≫
        ProSeq.ofMap (Functor.whiskerLeft TX Triangle.π₁Toπ₂) :=
  extensionByZero_map_comp_comparison jstar A _ _ _ _ fun n => (e.hom.app n).comm₁

omit [Preadditive 𝒞] [Preadditive 𝒟] in
/-- **`Rj_!` on the second map of a triangle.** -/
public lemma extensionByZero_map_mor₂_comp_comparison :
    (extensionByZero jstar A).map T.mor₂ ≫
        extensionByZeroComparison jstar A (mapTriangleConstIsoπ₃ jstar e) =
      extensionByZeroComparison jstar A (mapTriangleConstIsoπ₂ jstar e) ≫
        ProSeq.ofMap (Functor.whiskerLeft TX Triangle.π₂Toπ₃) :=
  extensionByZero_map_comp_comparison jstar A _ _ _ _ fun n => (e.hom.app n).comm₂

omit [Preadditive 𝒞] [Preadditive 𝒟] in
/-- **`Rj_!` on the third map of a triangle**, whose target is the shifted first vertex. -/
public lemma extensionByZero_map_mor₃_comp_comparison :
    (extensionByZero jstar A).map T.mor₃ ≫
        extensionByZeroComparison jstar A (mapTriangleConstIsoShiftπ₁ jstar e) =
      extensionByZeroComparison jstar A (mapTriangleConstIsoπ₃ jstar e) ≫
        ProSeq.ofMap (Functor.whiskerLeft TX Triangle.π₃Toπ₁) :=
  extensionByZero_map_comp_comparison jstar A _ _ _ _ fun n => by
    have h := (e.hom.app n).comm₃
    simp only [mapTriangleConstIsoShiftπ₁, mapTriangleConstIsoπ₁, mapTriangleConstIsoπ₃,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.constComp_hom_app, Category.id_comp, Category.comp_id,
      Iso.symm_hom]
    exact (Category.assoc _ _ _).symm.trans h

end Triangles

end CategoryTheory

namespace AlgebraicGeometry

variable {U X : Scheme.{u}}

/-- Morphisms into a restriction are the same read in `D^b_{Coh}(𝒪_U)` or in `D(𝒪_U)`, since
`D^b_{Coh}(𝒪_U)` is a full subcategory. -/
public def restrictBoundedCoherentLiftHomIso (j : U ⟶ X) [IsOpenImmersion j]
    [IsLocallyNoetherian X] (K : BoundedCoherentDerived U) :
    restrictBoundedCoherentLift j ⋙ coyoneda.obj (op K) ≅
      restrictBoundedCoherent j ⋙ coyoneda.obj (op ((boundedCoherentDerived U).ι.obj K)) :=
  NatIso.ofComponents (fun _ => (boundedCoherentDerived U).fullyFaithfulι.homEquiv.toIso)
    (fun _ => rfl)

variable (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]

/-- **The extension by zero `Rj_! : D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_X)`** along an open immersion
`j` of Noetherian schemes, [Stacks, Tag 0G4N]: it sends `K` to the pro-object of a Deligne system
with value `K`, the one of the assignment `AlgebraicGeometry.DeligneSystem.values`. Its functor of
points at `K` is `L ↦ Hom_U(K, L|_U)`. The value at `K` is the pro-object of any Deligne system
with value `K`, by `AlgebraicGeometry.DeligneSystem.Value.extensionByZeroIso`, and on morphisms
it is computed on any morphism of inverse systems restricting to the given one, by
`CategoryTheory.extensionByZero_map_comp_comparison`. -/
@[stacks 0G4N "the functor Rj_!"]
public def extensionByZeroOpenImmersion :
    BoundedCoherentDerived U ⥤ ProSeq (BoundedCoherentDerived X) :=
  extensionByZero (restrictBoundedCoherentLift j) (DeligneSystem.values j).toAssignment

variable {j}

namespace DeligneSystem

/-- A Deligne system `D` together with an identification `e` of `(K_n|_U)` with the constant
system at `K` has value `K`: the identification of [Stacks, Tag 0G2H] holds for it, by
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans`. -/
public def valueOfIso (D : DeligneSystem j) (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K)) : D.Value where
  obj := K
  constIso := e
  isIso_restrictionNatTrans := D.isIso_restrictionNatTrans K e

/-- The value of `AlgebraicGeometry.DeligneSystem.valueOfIso D K e` is `K`. -/
public lemma valueOfIso_obj (D : DeligneSystem j) (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K)) :
    (D.valueOfIso K e).obj = K :=
  rfl

/-- The identification recorded in `AlgebraicGeometry.DeligneSystem.valueOfIso D K e` is `e`. -/
public lemma valueOfIso_constIso (D : DeligneSystem j) (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K)) :
    (D.valueOfIso K e).constIso = e :=
  rfl

section OfComplex

variable (I : X.IdealSheafData) (hI : (I.support : Set X) = (Set.range j.base)ᶜ)
  (F : CochainComplex X.Modules ℤ) (hFge : ∃ a : ℤ, F.IsStrictlyGE a)
  (hFle : ∃ b : ℤ, F.IsStrictlyLE b) (hFcoh : ∀ i : ℤ, (F.X i).IsCoherent)

/-- For the Deligne system `(𝓘^n 𝓕^•)` of a bounded complex of coherent modules, the
identification of the restricted system with the constant system at `𝓕^•|_U` is, at `n`, the
restriction of the inclusion `𝓘^n 𝓕^• ⟶ 𝓕^•`. -/
public lemma ofComplex_restrictIsoConst_hom_app (n : ℕ) :
    (DeligneTriangle.deligneSystemOfComplex j I hI F hFge hFle hFcoh).restrictIsoConst.hom.app
        (op n) =
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.map
        (DerivedCategory.Q.map ((idealPowerComplexSystem I F).inclusion n)) := by
  simp only [DeligneTriangle.deligneSystemOfComplex, Functor.comp_obj, ObjectProperty.ι_obj,
    ObjectProperty.lift_obj_obj, Functor.const_obj_obj, restrictIsoConst,
    Functor.isoWhiskerRight_refl, inclusionNatTrans, Iso.refl_trans, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp]
  exact Category.comp_id _

/-- **The value of the Deligne system `(𝓘^n 𝓕^•)`.** An identification `φ` of `𝓕^•|_U` with an
object `K` of `D^b_{Coh}(𝒪_U)` makes `K` the value of the system. -/
public def ofComplexValue (K : BoundedCoherentDerived U)
    (φ : (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj (DerivedCategory.Q.obj F) ≅
      (boundedCoherentDerived U).ι.obj K) :
    (DeligneTriangle.deligneSystemOfComplex j I hI F hFge hFle hFcoh).Value :=
  (DeligneTriangle.deligneSystemOfComplex j I hI F hFge hFle hFcoh).valueOfIso K
    ((DeligneTriangle.deligneSystemOfComplex j I hI F hFge hFle hFcoh).restrictIsoConst ≪≫
      (Functor.const ℕᵒᵖ).mapIso φ)

/-- The value of `AlgebraicGeometry.DeligneSystem.ofComplexValue` is the object one started
with. -/
public lemma ofComplexValue_obj (K : BoundedCoherentDerived U)
    (φ : (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj (DerivedCategory.Q.obj F) ≅
      (boundedCoherentDerived U).ι.obj K) :
    (ofComplexValue I hI F hFge hFle hFcoh K φ).obj = K :=
  rfl

/-- For the value `AlgebraicGeometry.DeligneSystem.ofComplexValue` of `(𝓘^n 𝓕^•)` attached to
`φ`, the identification of `K` with `K_n|_U`, followed by the restriction of the inclusion
`𝓘^n 𝓕^• ⟶ 𝓕^•`, is `φ⁻¹`. -/
public lemma ofComplexValue_constIso_inv_app_comp (K : BoundedCoherentDerived U)
    (φ : (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj (DerivedCategory.Q.obj F) ≅
      (boundedCoherentDerived U).ι.obj K) (n : ℕ) :
    (ofComplexValue I hI F hFge hFle hFcoh K φ).constIso.inv.app (op n) ≫
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.map
        (DerivedCategory.Q.map ((idealPowerComplexSystem I F).inclusion n)) = φ.inv := by
  have h := ofComplex_restrictIsoConst_hom_app I hI F hFge hFle hFcoh n
  show (φ.inv ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun t => φ.inv ≫ t)
    ((congrArg (fun t => _ ≫ t) h.symm).trans (Iso.inv_hom_id_app _ _))).trans
      (Category.comp_id _))

end OfComplex

namespace Value

variable {D : DeligneSystem j} (V : D.Value)

/-- [Stacks, Tag 0G2H] for a Deligne system with value `K`, as an identification of functors of
points `Hom_U(K, j^* -) ≅ colim_n Hom_X(K_n, -)`, morphisms on `U` being read in
`D^b_{Coh}(𝒪_U)`. -/
public def pointsIso :
    restrictBoundedCoherentLift j ⋙ coyoneda.obj (op V.obj) ≅
      Pro.coyonedaColim (Pro.liftedInverseSequence D.system) :=
  restrictBoundedCoherentLiftHomIso j V.obj ≪≫ V.homIso.symm

/-- The identification `AlgebraicGeometry.DeligneSystem.Value.pointsIso` sends the class of
`g : K_n ⟶ L` to the restriction of `g` to `U`, read through the identification of `K` with
`K_n|_U`. -/
public lemma pointsIso_inv_app_ι (i : (ULiftHom.{u + 1} (ULift.{u + 1} ℕᵒᵖ))ᵒᵖ)
    (L : BoundedCoherentDerived X)
    (g : (Pro.liftedInverseSequence D.system).obj (unop i) ⟶ L) :
    V.pointsIso.inv.app L
        ((colimit.ι ((Pro.liftedInverseSequence D.system).op ⋙ coyoneda) i).app L g) =
      (ObjectProperty.homMk (V.constIso.inv.app (Pro.liftedIndexDown i) ≫
        (restrictBoundedCoherent j).map g) : V.obj ⟶ (restrictBoundedCoherentLift j).obj L) :=
  ObjectProperty.hom_ext _ (D.restrictionNatTrans_app_ι V.obj V.constIso i L g)

/-- **`Rj_! K` is the pro-object of any Deligne system with value `K`.** Both have the functor of
points `L ↦ Hom_U(K, L|_U)`, by [Stacks, Tag 0G2H]; the identification is the restriction map. -/
@[stacks 0G4N "Rj_! K is the pro-object of any Deligne system with value K"]
public def extensionByZeroIso : D.proObject ≅ (extensionByZeroOpenImmersion j).obj V.obj :=
  (ObjectProperty.isoMk (IsSequentialProObject (BoundedCoherentDerived X))
    (X := ((extensionByZeroOpenImmersion j).obj V.obj).unop) (Y := D.proObject.unop)
    V.pointsIso).op

/-- On functors of points, `AlgebraicGeometry.DeligneSystem.Value.extensionByZeroIso` is the
identification `AlgebraicGeometry.DeligneSystem.Value.pointsIso`. -/
public lemma extensionByZeroIso_hom_unop_hom :
    V.extensionByZeroIso.hom.unop.hom = V.pointsIso.hom :=
  rfl

/-- On functors of points, the inverse of
`AlgebraicGeometry.DeligneSystem.Value.extensionByZeroIso` is the inverse of
`AlgebraicGeometry.DeligneSystem.Value.pointsIso`. -/
public lemma extensionByZeroIso_inv_unop_hom :
    V.extensionByZeroIso.inv.unop.hom = V.pointsIso.inv :=
  rfl

end Value

end DeligneSystem

section Properties

variable (j)

/-- **Stacks Project, Tag 0G4N**, adjointness. `Rj_!` is "left adjoint" to
`j^* : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_U)`: morphisms of pro-objects from `Rj_! K` to the constant
pro-object at `L` are the morphisms `K ⟶ L|_U`,

`Hom_{Pro}(Rj_! K, L) = Hom_U(K, L|_U)`,

naturally in `K` and in `L`. Both sides are the functor of points of `Rj_! K` at `L`, which is
`colim_n Hom_X(K_n, L)` for a Deligne system `(K_n)` with restriction `K`, and the identification
with `Hom_U(K, L|_U)` is Stacks 0G2H. -/
@[stacks 0G4N "Rj_! is left adjoint to j^*"]
public def extensionByZeroOpenImmersionHomIso :
    (extensionByZeroOpenImmersion j).op ⋙ coyoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj ProSeq.const ≅
      coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (restrictBoundedCoherentLift j) :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun L => (extensionByZeroHomEquiv _ (DeligneSystem.values j).toAssignment K.unop L).toIso)
      (fun {L L'} ψ => by
        ext f
        exact extensionByZeroHomEquiv_comp_const _ (DeligneSystem.values j).toAssignment ψ
          K.unop f))
    (fun {K K'} φ => by
      ext L f
      exact extensionByZeroHomEquiv_comp_map _ (DeligneSystem.values j).toAssignment φ.unop L f)

/-- The adjointness isomorphism is the bijection `CategoryTheory.extensionByZeroHomEquiv`. -/
public lemma extensionByZeroOpenImmersionHomIso_hom_app_app (K : BoundedCoherentDerived U)
    (L : BoundedCoherentDerived X)
    (f : (extensionByZeroOpenImmersion j).obj K ⟶ ProSeq.const.obj L) :
    ((extensionByZeroOpenImmersionHomIso j).hom.app (op K)).app L f =
      extensionByZeroHomEquiv _ (DeligneSystem.values j).toAssignment K L f :=
  rfl

/-- **Stacks Project, Tag 0G4N**, exactness. Let `K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle
`T` of `D^b_{Coh}(𝒪_U)`. Then there is an inverse system of distinguished triangles
`K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]` of `D^b_{Coh}(𝒪_X)`, with an identification `e` of its restriction to
`U` with the constant system at `T`, whose vertex systems `(K_n)`, `(L_n)`, `(M_n)` are Deligne
systems, and such that `Rj_!` sends `T` to its pro-system: the comparison maps

`Rj_! K ⟶ (K_n)`, `Rj_! L ⟶ (L_n)`, `Rj_! M ⟶ (M_n)`, `Rj_!(K[1]) ⟶ (K_n[1])`

induced by `e` are isomorphisms of pro-objects, and they carry `Rj_!` of the three maps of `T` to
the morphisms of pro-systems induced by the three maps of the triangles.

The system is the one of Stacks 0G4M; the comparison maps are isomorphisms by Stacks 0G2H, which
holds for the vertex systems because they are Deligne systems, and for `(K_n[1])` because it holds
for `(K_n)`. -/
@[stacks 0G4N "Rj_! is exact"]
public theorem extensionByZeroOpenImmersion_exact (T : Triangle (BoundedCoherentDerived U))
    (hT : T ∈ distTriang (BoundedCoherentDerived U)) :
    ∃ (TX : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X))
      (e : TX ⋙ (restrictBoundedCoherentLift j).mapTriangle ≅ (Functor.const ℕᵒᵖ).obj T),
      (∀ n, TX.obj n ∈ distTriang (BoundedCoherentDerived X)) ∧
      (∃ D : DeligneSystem j, Nonempty (TX ⋙ Triangle.π₁ ≅ D.system)) ∧
      (∃ D : DeligneSystem j, Nonempty (TX ⋙ Triangle.π₂ ≅ D.system)) ∧
      (∃ D : DeligneSystem j, Nonempty (TX ⋙ Triangle.π₃ ≅ D.system)) ∧
      IsIso (extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
        (mapTriangleConstIsoπ₁ _ e)) ∧
      IsIso (extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
        (mapTriangleConstIsoπ₂ _ e)) ∧
      IsIso (extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
        (mapTriangleConstIsoπ₃ _ e)) ∧
      IsIso (extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
        (mapTriangleConstIsoShiftπ₁ _ e)) ∧
      (extensionByZeroOpenImmersion j).map T.mor₁ ≫
          extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
            (mapTriangleConstIsoπ₂ _ e) =
        extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
            (mapTriangleConstIsoπ₁ _ e) ≫
          ProSeq.ofMap (Functor.whiskerLeft TX Triangle.π₁Toπ₂) ∧
      (extensionByZeroOpenImmersion j).map T.mor₂ ≫
          extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
            (mapTriangleConstIsoπ₃ _ e) =
        extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
            (mapTriangleConstIsoπ₂ _ e) ≫
          ProSeq.ofMap (Functor.whiskerLeft TX Triangle.π₂Toπ₃) ∧
      (extensionByZeroOpenImmersion j).map T.mor₃ ≫
          extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
            (mapTriangleConstIsoShiftπ₁ _ e) =
        extensionByZeroComparison _ (DeligneSystem.values j).toAssignment
            (mapTriangleConstIsoπ₃ _ e) ≫
          ProSeq.ofMap (Functor.whiskerLeft TX Triangle.π₃Toπ₁) := by
  obtain ⟨DK, DL, DM, TX, hTX, ⟨eK⟩, ⟨eL⟩, ⟨eM⟩, ⟨e⟩⟩ :=
    DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent j T hT
  set R := restrictBoundedCoherentLift j with hR
  set A := (DeligneSystem.values j).toAssignment with hA
  have lift : ∀ {D : DeligneSystem j} {S : ℕᵒᵖ ⥤ BoundedCoherentDerived X}, (S ≅ D.system) →
      ∀ N, RestrictionLifting S R N := fun {D} _ eS N =>
    (D.restrictionLifting_lift N).of_natIso eS R N
  have hK := lift eK
  have hL := lift eL
  have hM := lift eM
  have hK' : ∀ N, RestrictionLifting
      (TX ⋙ Triangle.π₁ ⋙ shiftFunctor (BoundedCoherentDerived X) (1 : ℤ)) R N := fun N =>
    (hK (N⟦(-1 : ℤ)⟧)).map_source (shiftFunctor _ (1 : ℤ)) (shiftFunctor _ (1 : ℤ)) R
      (R.commShiftIso (1 : ℤ))
      ((shiftFunctorCompIsoId (BoundedCoherentDerived X) (-1 : ℤ) 1 (by decide)).app N)
  refine ⟨TX, e, hTX, ⟨DK, ⟨eK⟩⟩, ⟨DL, ⟨eL⟩⟩, ⟨DM, ⟨eM⟩⟩,
    (extensionByZeroComparisonIso R A _ hK).isIso_hom,
    (extensionByZeroComparisonIso R A _ hL).isIso_hom,
    (extensionByZeroComparisonIso R A _ hM).isIso_hom,
    (extensionByZeroComparisonIso R A _ hK').isIso_hom,
    extensionByZero_map_mor₁_comp_comparison R A e,
    extensionByZero_map_mor₂_comp_comparison R A e,
    extensionByZero_map_mor₃_comp_comparison R A e⟩

end Properties

end AlgebraicGeometry

end
