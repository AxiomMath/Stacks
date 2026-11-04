module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.AlgebraicallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableEquivalence

/-!
# The stalk functor at a geometric point is a pullback functor

Let `X` be an algebraic space over `S` and let `x` be a geometric point of `X`, that is a
morphism `Spec(k) ⟶ X` with `k` an algebraically closed field. The geometric point is in
particular a morphism of algebraic spaces from the space represented by `Spec(k)`, so it
induces a morphism of small étale topoi; this file identifies the stalk functor at `x` with
the inverse image along that morphism, followed by global sections. Global sections on the
source is an equivalence onto sets, so the stalk functor loses nothing.

This is [Stacks, Tag 04K3], the analogue for algebraic spaces of [Stacks, Tag 04JN].

## Main definitions

* `AlgebraicGeometry.Space.idChart`: the identity chart of a representable presheaf, the
  terminal object of its small étale site.
* `AlgebraicGeometry.Space.tautologicalGeometricPoint`: the geometric point of the presheaf
  represented by the field spectrum of a geometric point, given by the identity.

## Main results

* `AlgebraicGeometry.Space.smallEtaleStalkIsoPullbackGlobalSections`: the stalk functor at a
  geometric point is the inverse image along it followed by global sections.
* `AlgebraicGeometry.Space.globalSections_isEquivalence_of_geometricPoint`: on the small étale
  site of the algebraic space represented by the field spectrum of a geometric point, global
  sections is an equivalence onto sets.
* `AlgebraicGeometry.Space.isTerminal_idChart` and
  `AlgebraicGeometry.Space.isInitial_idNeighborhood`: the identity chart is terminal in the
  small étale site of a representable presheaf, and carries the initial étale neighbourhood
  of the tautological geometric point.

## References

* [Stacks Project, Tag 04K3](https://stacks.math.columbia.edu/tag/04K3)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/-- The quotient colimit `CategoryTheory.Functor.ColimitType` of a diagram of types over a
category with a terminal object `T` is the value of the diagram at `T`. -/
def Functor.colimitTypeEquivOfTerminal {J : Type u} [Category.{v} J] {F : J ⥤ Type w}
    (T : J) (hT : Limits.IsTerminal T) : F.ColimitType ≃ F.obj T where
  toFun := Quot.lift (fun p : Σ j, F.obj j => F.map (hT.from p.1) p.2) (by
    rintro ⟨j, a⟩ ⟨k, b⟩ ⟨g, hg⟩
    change b = F.map g a at hg
    calc
      F.map (hT.from j) a = F.map (g ≫ hT.from k) a := by rw [hT.hom_ext (g ≫ hT.from k)]
      _ = F.map (hT.from k) (F.map g a) := by rw [Functor.map_comp]; rfl
      _ = F.map (hT.from k) b := by rw [← hg])
  invFun := F.ιColimitType T
  left_inv z := by
    induction z using Quot.inductionOn with
    | _ p =>
      obtain ⟨j, a⟩ := p
      exact F.ιColimitType_eq_of_map_eq_map _ _ (𝟙 T) (hT.from j) (by simp)
  right_inv a := by
    change F.map (hT.from T) a = a
    rw [hT.hom_ext (hT.from T) (𝟙 T)]
    simp

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The identity chart of a representable presheaf -/

/-- The identity of `yoneda.obj T` is an étale chart of `yoneda.obj T`. -/
theorem isEtaleChart_id (T : BigFppfOver B S hS) :
    IsEtaleChart B S hS (yoneda.obj T) (CostructuredArrow.mk (𝟙 (yoneda.obj T))) :=
  presheaf_etale_id B S hS T

/-- The identity chart of a representable presheaf: the object of the small étale site of
`yoneda.obj T` given by the identity of `yoneda.obj T`. -/
def idChart (T : BigFppfOver B S hS) : SmallEtale B S hS (yoneda.obj T) :=
  ⟨CostructuredArrow.mk (𝟙 (yoneda.obj T)), isEtaleChart_id B S hS T⟩

/-- The identity chart is the terminal object of the small étale site of a representable
presheaf. -/
def isTerminal_idChart (T : BigFppfOver B S hS) : IsTerminal (idChart B S hS T) := by
  have hmap (V : SmallEtale B S hS (yoneda.obj T)) (g : V.obj.left ⟶ T) :
      yoneda.map g ≫ (idChart B S hS T).obj.hom = V.obj.hom ↔ g = yonedaEquiv V.obj.hom := by
    rw [show (idChart B S hS T).obj.hom = 𝟙 (yoneda.obj T) from rfl, Category.comp_id]
    exact ⟨fun h => by rw [← h, yonedaEquiv_yoneda_map],
      fun h => h ▸ yonedaEquiv.injective (yonedaEquiv_yoneda_map _)⟩
  refine IsTerminal.ofUniqueHom
    (fun V => ObjectProperty.homMk
      (CostructuredArrow.homMk (yonedaEquiv V.obj.hom) ((hmap V _).2 rfl))) ?_
  exact fun V m => ObjectProperty.hom_ext _
    (CostructuredArrow.hom_ext _ _ ((hmap V m.hom.left).1 (CostructuredArrow.w m.hom)))

/-- The small étale site of a representable presheaf has a terminal object. -/
instance hasTerminal_smallEtale_yoneda (T : BigFppfOver B S hS) :
    HasTerminal (SmallEtale B S hS (yoneda.obj T)) :=
  (isTerminal_idChart B S hS T).hasTerminal

/-! ### The tautological geometric point -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The geometric point of the presheaf represented by the field spectrum of a geometric
point `x`, given by the identity morphism. -/
def tautologicalGeometricPoint (x : GeometricPoint B S hS F) :
    GeometricPoint B S hS (yoneda.obj x.val.siteObject) :=
  ⟨x.val.tautologicalPoint B S hS F, x.property⟩

/-- The morphism presented by a field-valued point carries the tautological point of the
represented presheaf back to that point. -/
theorem map_fieldMorphism_tautologicalPoint (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint.map B S hS (yoneda.obj p.siteObject) (fieldMorphism B S hS F p)
        (p.tautologicalPoint B S hS F) = p := by
  obtain ⟨carrier, contained, toBase, value⟩ := p
  simp only [FieldValuedPoint.map, FieldValuedPoint.mk.injEq, heq_eq_eq, true_and]
  exact yonedaEquiv_fieldMorphism B S hS F _

/-- The morphism presented by a geometric point carries the tautological geometric point of
the represented presheaf back to that geometric point. -/
theorem geometricPointMap_fieldMorphism_tautological (x : GeometricPoint B S hS F) :
    geometricPointMap (fieldMorphism B S hS F x.val) (tautologicalGeometricPoint B S hS x) =
      x :=
  Subtype.ext (map_fieldMorphism_tautologicalPoint B S hS x.val)

/-- The identity chart, with the identity as lift, as an étale neighbourhood of the
tautological geometric point. -/
def idNeighborhood (x : GeometricPoint B S hS F) :
    SmallEtaleNeighborhood (tautologicalGeometricPoint B S hS x) where
  chart := idChart B S hS x.val.siteObject
  point := 𝟙 x.val.siteObject
  point_comp := rfl

/-- The identity chart with its identity lift is the initial étale neighbourhood of the
tautological geometric point. -/
def isInitial_idNeighborhood (x : GeometricPoint B S hS F) :
    IsInitial (idNeighborhood B S hS x) := by
  refine IsInitial.ofUniqueHom (fun V => ?_) ?_
  · refine { hom := ObjectProperty.homMk (CostructuredArrow.homMk V.point ?_), point_comp := ?_ }
    · exact yonedaEquiv.injective V.point_comp
    · exact Category.id_comp V.point
  · intro V m
    apply SmallEtaleNeighborhood.Hom.ext
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact (Category.id_comp m.hom.hom.left).symm.trans m.point_comp

/-! ### The stalk at the tautological point is global sections -/

/-- The stalk at the tautological geometric point is evaluation at the identity chart. -/
def tautologicalStalkIsoEvaluation (x : GeometricPoint B S hS F) :
    (stalkSetFunctor (tautologicalGeometricPoint B S hS x) :
        ((SmallEtale B S hS (yoneda.obj x.val.siteObject))ᵒᵖ ⥤ Type (u + 1)) ⥤
          Type (u + 1)) ≅
      (evaluation (SmallEtale B S hS (yoneda.obj x.val.siteObject))ᵒᵖ (Type (u + 1))).obj
        (Opposite.op (idChart B S hS x.val.siteObject)) := by
  refine NatIso.ofComponents (fun P => Equiv.toIso
    (Functor.colimitTypeEquivOfTerminal (F := SmallEtaleNeighborhood.sections (x := _) P)
      (Opposite.op (idNeighborhood B S hS x)) (isInitial_idNeighborhood B S hS x).op)) ?_
  intro P Q α
  ext z
  induction z using Quot.inductionOn with
  | _ p =>
    obtain ⟨V, a⟩ := p
    let g := (isInitial_idNeighborhood B S hS x).op.from V
    change Q.map g.unop.hom.op (α.app (Opposite.op V.unop.chart) a) =
      α.app (Opposite.op (idNeighborhood B S hS x).chart) (P.map g.unop.hom.op a)
    simpa only [types_comp_apply] using
      congrArg (fun k => k a) (α.naturality g.unop.hom.op).symm

/-- Global sections on the small étale site of the presheaf represented by the field spectrum
of a geometric point is the stalk at the tautological geometric point. -/
def globalSectionsIsoTautologicalStalk (x : GeometricPoint B S hS F) :
    Sheaf.Γ (SmallEtale.topology B S hS (yoneda.obj x.val.siteObject)) (Type (u + 1)) ≅
      sheafToPresheaf (SmallEtale.topology B S hS (yoneda.obj x.val.siteObject))
          (Type (u + 1)) ⋙
        stalkSetFunctor (tautologicalGeometricPoint B S hS x) :=
  Sheaf.ΓNatIsoSheafSections _ _ (isTerminal_idChart B S hS x.val.siteObject) ≪≫
    Functor.isoWhiskerLeft _ (tautologicalStalkIsoEvaluation B S hS x).symm

/-- Global sections is an equivalence from sheaves of sets on the small étale site of the
algebraic space represented by the field spectrum of a geometric point onto sets. -/
@[stacks 04K3 "equivalence by global sections", sga "4½ Arcata 2.4.4" "sep. closed field, G=1"]
theorem globalSections_isEquivalence_of_geometricPoint (x : GeometricPoint B S hS F) :
    (Sheaf.Γ (SmallEtale.topology B S hS (yoneda.obj x.val.siteObject))
      (Type (u + 1))).IsEquivalence := by
  let A := Type (u + 1)
  let T := x.val.siteObject
  let E := associatedBigEtaleSite B
  have hK : E.Contains (Spec (.of x.val.carrier)) := x.val.contained
  let e := representedSmallEtaleEquivalence B S hS T
  let J := SmallEtale.topology B S hS (yoneda.obj T)
  let K := _root_.AlgebraicGeometry.SmallEtale.topology E (Spec (.of x.val.carrier)) hK
  have htop : e.functor.inducedTopology K = J :=
    representedSmallEtaleEquivalence_topology B S hS T
  have : e.inverse.IsDenseSubsite K J := by
    rw [← htop]
    exact inferInstanceAs
      (e.symm.functor.IsDenseSubsite K (e.symm.inverse.inducedTopology K))
  let cK := _root_.AlgebraicGeometry.SmallEtale.final E (Spec (.of x.val.carrier)) hK
  have hcK : IsTerminal cK :=
    _root_.AlgebraicGeometry.SmallEtale.finalIsTerminal E (Spec (.of x.val.carrier)) hK
  let i : e.inverse.obj cK ≅ idChart B S hS T :=
    (hcK.isTerminalObj e.inverse).uniqueUpToIso (isTerminal_idChart B S hS T)
  have : IsAlgClosed x.val.carrier := x.property
  have hΓK : (Sheaf.Γ K A).IsEquivalence :=
    globalSections_isEquivalence_of_isAlgClosed E x.val.carrier hK
  let SC := Equivalence.sheafCongr J K e A
  let θ : (sheafSections J A).obj (Opposite.op (idChart B S hS T)) ≅
      SC.functor ⋙ (sheafSections K A).obj (Opposite.op cK) :=
    NatIso.ofComponents (fun G => G.obj.mapIso i.op)
      (fun α => (α.hom.naturality i.op.hom).symm)
  have hiso : Sheaf.Γ J A ≅ SC.functor ⋙ Sheaf.Γ K A :=
    Sheaf.ΓNatIsoSheafSections J A (isTerminal_idChart B S hS T) ≪≫ θ ≪≫
      Functor.isoWhiskerLeft SC.functor (Sheaf.ΓNatIsoSheafSections K A hcK).symm
  exact Functor.isEquivalence_of_iso hiso.symm

/-! ### Stalks as pullbacks -/

variable {X : AlgebraicSpaces B S hS}

/-- The stalk functor at a geometric point `x` of an algebraic space `X` is the inverse image
along `x` — viewed as a morphism of algebraic spaces from the space represented by its field
spectrum, hence as a morphism of small étale topoi — followed by global sections on the source. -/
@[stacks 04K3 "the stalk as global sections of the pullback"]
def smallEtaleStalkIsoPullbackGlobalSections (x : GeometricPoint B S hS X.obj) :
    sheafToPresheaf (SmallEtale.topology B S hS X.obj) (Type (u + 1)) ⋙ stalkSetFunctor x ≅
      (smallToposMorphism B S hS
            (ObjectProperty.homMk (fieldMorphism B S hS X.obj x.val) :
              (⟨yoneda.obj x.val.siteObject,
                  isAlgebraicSpace_yoneda B S hS x.val.siteObject⟩ :
                AlgebraicSpaces B S hS) ⟶ X)).inverseImage ⋙
        Sheaf.Γ (SmallEtale.topology B S hS (yoneda.obj x.val.siteObject))
          (Type (u + 1)) := by
  let P : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj x.val.siteObject, isAlgebraicSpace_yoneda B S hS x.val.siteObject⟩
  let f : P ⟶ X := ObjectProperty.homMk (fieldMorphism B S hS X.obj x.val)
  let y : GeometricPoint B S hS P.obj := tautologicalGeometricPoint B S hS x
  have hxy : geometricPointMap f.hom y = x :=
    geometricPointMap_fieldMorphism_tautological B S hS x
  have hstalk : (stalkSetFunctor (geometricPointMap f.hom y) :
      ((SmallEtale B S hS X.obj)ᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)) =
      stalkSetFunctor x := by rw [hxy]
  exact Functor.isoWhiskerLeft _ (eqToIso hstalk).symm ≪≫
    (smallEtaleInverseImageStalkIso B S hS f y).symm ≪≫
    Functor.isoWhiskerLeft (smallToposMorphism B S hS f).inverseImage
      (globalSectionsIsoTautologicalStalk B S hS x).symm

end AlgebraicGeometry.Space

end
