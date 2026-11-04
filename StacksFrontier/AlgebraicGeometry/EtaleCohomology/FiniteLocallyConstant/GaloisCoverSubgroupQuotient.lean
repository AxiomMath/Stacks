module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisCoverDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.RingTheory.Branches.Defs
public import StacksFrontier.RingTheory.Etale.Basic

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.PointedGaloisCovering

/-!
# The quotient of a Galois cover by a subgroup of its automorphism group

Let `C` be a Galois category with a fibre functor `F`, let `A` be a connected object of `C` and
let `H` be a subgroup of `Aut A`. The quotient `A/H` is the colimit of the action of `H` on `A`.
The fibre functor preserves it, so `F(A) ⟶ F(A/H)` is surjective and identifies two points of
`F(A)` exactly when they lie in one `H`-orbit; if `A` is Galois, `F(A/H)` has `[Aut A : H]`
points.

For a pointed Galois cover `A` of an irreducible, geometrically unibranch scheme `S`, this makes
`A ⟶ A/H` a Galois covering of `A/H` with group `H`, in the sense of
`AlgebraicGeometry.EtaleGaloisCovering`.

## Main definitions

* `CategoryTheory.PreGaloisCategory.subgroupQuotient` — the quotient `A/H`.
* `AlgebraicGeometry.PointedGaloisCover.subgroupQuotientCovering` — `A ⟶ A/H` as a Galois
  covering of `A/H` with group `H`.

## Main results

* `CategoryTheory.PreGaloisCategory.exists_eq_of_map_subgroupQuotientι_eq` and
  `CategoryTheory.PreGaloisCategory.surjective_map_subgroupQuotientι` — the fibre of `A/H` is the
  set of `H`-orbits of the fibre of `A`.
* `CategoryTheory.PreGaloisCategory.natCard_fiber_subgroupQuotient` — the fibre of `A/H` has
  `[Aut A : H]` points.

## References

* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2)
* [Stacks Project, Tag 0GJ0](https://stacks.math.columbia.edu/tag/0GJ0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe u u₁ u₂ w

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (X : C) [IsConnected X]
  (H : Subgroup (Aut X))

/-- The action of a subgroup `H` of `Aut X` on `X`, as a diagram indexed by `H`. -/
abbrev subgroupQuotientDiagram : SingleObj H ⥤ C :=
  SingleObj.functor ((Aut.toEnd X).comp H.subtype)

/-- **The quotient `X/H`** of a connected object of a Galois category by a subgroup of its
automorphism group. -/
abbrev subgroupQuotient : C :=
  colimit (subgroupQuotientDiagram X H)

/-- The quotient map `X ⟶ X/H`. -/
abbrev subgroupQuotientι : X ⟶ subgroupQuotient X H :=
  colimit.ι (subgroupQuotientDiagram X H) (SingleObj.star H)

/-- The quotient map is invariant under `H`. -/
theorem hom_comp_subgroupQuotientι (h : H) :
    (h : Aut X).hom ≫ subgroupQuotientι X H = subgroupQuotientι X H :=
  colimit.w (subgroupQuotientDiagram X H) (h : SingleObj.star H ⟶ SingleObj.star H)

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- The fibre functor carries the quotient map to the quotient of the fibre by the action of `H`:
the composite of `F(X) ⟶ F(X/H)` with the comparison of `F(X/H)` with the colimit in types is the
projection to the orbit space. -/
private theorem exists_equiv_orbitRel :
    ∃ e : (F ⋙ FintypeCat.incl).obj (subgroupQuotient X H) ≃
        MulAction.orbitRel.Quotient H
          ((subgroupQuotientDiagram X H ⋙ F ⋙ FintypeCat.incl).obj (SingleObj.star H)),
      ∀ a : F.obj X, e ((F ⋙ FintypeCat.incl).map (subgroupQuotientι X H) a) =
        (⟦a⟧ : MulAction.orbitRel.Quotient H
          ((subgroupQuotientDiagram X H ⋙ F ⋙ FintypeCat.incl).obj (SingleObj.star H))) := by
  let G := F ⋙ FintypeCat.incl
  let J := subgroupQuotientDiagram X H
  let hc : IsColimit (G.mapCocone (colimit.cocone J)) :=
    isColimitOfPreserves G (colimit.isColimit J)
  refine ⟨(hc.coconePointUniqueUpToIso (colimit.isColimit (J ⋙ G))).toEquiv.trans
    (Limits.SingleObj.Types.colimitEquivQuotient (J ⋙ G)), fun a ↦ ?_⟩
  have h1 : (hc.coconePointUniqueUpToIso (colimit.isColimit (J ⋙ G))).hom
      (G.map (subgroupQuotientι X H) a) = colimit.ι (J ⋙ G) (SingleObj.star H) a :=
    ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom hc _ (SingleObj.star H)) a
  show Limits.SingleObj.Types.colimitEquivQuotient (J ⋙ G)
    ((hc.coconePointUniqueUpToIso (colimit.isColimit (J ⋙ G))).hom
      (G.map (subgroupQuotientι X H) a)) = _
  rw [h1]
  have h2 : Types.colimitEquivColimitType (J ⋙ G) (colimit.ι (J ⋙ G) (SingleObj.star H) a) =
      Quot.mk _ ⟨SingleObj.star H, a⟩ :=
    Types.colimitEquivColimitType_apply _ _ _
  exact congrArg (Limits.SingleObj.colimitTypeRelEquivOrbitRelQuotient (J ⋙ G)) h2

/-- **Two points of the fibre of `X` with the same image in the fibre of `X/H` lie in one
`H`-orbit.** -/
theorem exists_eq_of_map_subgroupQuotientι_eq {a b : F.obj X}
    (hab : F.map (subgroupQuotientι X H) a = F.map (subgroupQuotientι X H) b) :
    ∃ h : H, F.map (h : Aut X).hom a = b := by
  obtain ⟨e, he⟩ := exists_equiv_orbitRel X H F
  have h1 : (⟦b⟧ : MulAction.orbitRel.Quotient H
      ((subgroupQuotientDiagram X H ⋙ F ⋙ FintypeCat.incl).obj (SingleObj.star H))) = ⟦a⟧ :=
    (he b).symm.trans ((congrArg e hab.symm).trans (he a))
  exact MulAction.mem_orbit_iff.1 (Quotient.exact h1)

/-- **The fibre of `X` maps onto the fibre of `X/H`.** -/
theorem surjective_map_subgroupQuotientι :
    Function.Surjective (F.map (subgroupQuotientι X H)) := by
  obtain ⟨e, he⟩ := exists_equiv_orbitRel X H F
  intro t
  obtain ⟨a, ha⟩ := Quotient.exists_rep (e t)
  exact ⟨a, e.injective ((he a).trans ha)⟩

/-- **The fibre of `X/H` has `[Aut X : H]` points when `X` is Galois.** -/
theorem natCard_fiber_subgroupQuotient [IsGalois X] :
    Nat.card (F.obj (subgroupQuotient X H)) = H.index := by
  classical
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F X
  let q := F.map (subgroupQuotientι X H)
  let sec := Function.surjInv (surjective_map_subgroupQuotientι X H F)
  have hsec : ∀ t, q (sec t) = t := Function.surjInv_eq (surjective_map_subgroupQuotientι X H F)
  have hq : ∀ (h : H) (y : F.obj X), q (F.map (h : Aut X).hom y) = q y := fun h y ↦ by
    show (F.map (h : Aut X).hom ≫ F.map (subgroupQuotientι X H)) y = _
    rw [← F.map_comp, hom_comp_subgroupQuotientι]
  let φ : F.obj (subgroupQuotient X H) × H → F.obj X := fun p ↦ F.map (p.2 : Aut X).hom (sec p.1)
  have hφ : Function.Bijective φ := by
    refine ⟨fun p p' hpp' ↦ ?_, fun y ↦ ?_⟩
    · have ht : p.1 = p'.1 := (hsec p.1).symm.trans ((hq p.2 _).symm.trans
        ((congrArg q hpp').trans ((hq p'.2 _).trans (hsec p'.1))))
      obtain ⟨p1, p2⟩ := p
      obtain ⟨p'1, p'2⟩ := p'
      simp only at ht
      subst ht
      refine Prod.ext rfl (Subtype.ext ?_)
      exact evaluation_aut_injective_of_isConnected F X (sec p1) hpp'
    · obtain ⟨h, hh⟩ := exists_eq_of_map_subgroupQuotientι_eq X H F (hsec (q y))
      exact ⟨⟨q y, h⟩, hh⟩
  have h1 : Nat.card (F.obj X) = Nat.card (F.obj (subgroupQuotient X H)) * Nat.card H := by
    rw [← Nat.card_prod]
    exact (Nat.card_eq_of_bijective φ hφ).symm
  have h2 : Nat.card (F.obj X) = Nat.card H * H.index := by
    rw [Subgroup.card_mul_index]
    exact (Nat.card_congr (evaluationEquivOfIsGalois F X a)).symm
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [h2, mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry

variable {S : Scheme.{u}} [IrreducibleSpace S] (hS : IsGeometricallyUnibranch S)
  {s : GeometricPoint S} (A : PointedGaloisCover s) (H : Subgroup (Aut A.obj))

/-- The quotient map of a pointed Galois cover by a subgroup of its automorphism group is étale. -/
instance etale_subgroupQuotientι_left : Etale (subgroupQuotientι A.obj H).left :=
  MorphismProperty.of_postcomp @Etale (W' := @Etale) (subgroupQuotientι A.obj H).left
    (subgroupQuotient A.obj H).hom (subgroupQuotient A.obj H).prop.2
    ((MorphismProperty.Over.w (subgroupQuotientι A.obj H)).symm ▸ A.obj.prop.2)

/-- **The quotient map `A ⟶ A/H` is surjective.** -/
theorem surjective_subgroupQuotientι_left :
    Function.Surjective (subgroupQuotientι A.obj H).left.base := by
  intro t
  let x' := ((subgroupQuotient A.obj H).left.algClosedPoint t).map
    (𝟙 _ ≫ (subgroupQuotient A.obj H).hom)
  let F := finiteEtaleFiberFintypeFunctor S x'
  obtain ⟨y, hy⟩ := surjective_map_subgroupQuotientι A.obj H F
    (fiberPointOfComp t (𝟙 (subgroupQuotient A.obj H).left))
  have hy' : y.1 ≫ (subgroupQuotientι A.obj H).left =
      ((subgroupQuotient A.obj H).left.algClosedPoint t).hom ≫ 𝟙 _ :=
    congrArg Subtype.val hy
  refine ⟨y.1.base default, ?_⟩
  rw [← Scheme.Hom.comp_apply, hy', Category.comp_id]
  exact Scheme.algClosedPointHom_apply _ t default

/-- **Two morphisms into `A` with the same composite to `A/H` differ by an element of `H` near
every point.** -/
theorem exists_mem_agreeLocus_subgroupQuotientι {W : Scheme.{u}} (a b : W ⟶ A.obj.left)
    (hab : a ≫ (subgroupQuotientι A.obj H).left = b ≫ (subgroupQuotientι A.obj H).left)
    (w : W) :
    ∃ (h : H) (hw : (a ≫ (h : Aut A.obj).hom.left) ≫ (subgroupQuotientι A.obj H).left =
        b ≫ (subgroupQuotientι A.obj H).left),
      w ∈ Scheme.Hom.agreeLocus (subgroupQuotientι A.obj H).left _ _ hw := by
  have hab' : a ≫ A.obj.hom = b ≫ A.obj.hom := by
    rw [← MorphismProperty.Over.w (subgroupQuotientι A.obj H), ← Category.assoc,
      ← Category.assoc]
    exact congrArg (· ≫ (subgroupQuotient A.obj H).hom) hab
  let x' := (W.algClosedPoint w).map (a ≫ A.obj.hom)
  let F := finiteEtaleFiberFintypeFunctor S x'
  let ea : F.obj A.obj := fiberPointOfComp (A := A.obj) w a
  let eb : F.obj A.obj := (⟨(W.algClosedPoint w).hom ≫ b, by
      rw [Category.assoc, ← hab']; rfl⟩ : finiteEtaleFiber x' A.obj)
  have hq : F.map (subgroupQuotientι A.obj H) ea = F.map (subgroupQuotientι A.obj H) eb := by
    apply Subtype.ext
    show ((W.algClosedPoint w).hom ≫ a) ≫ (subgroupQuotientι A.obj H).left =
      ((W.algClosedPoint w).hom ≫ b) ≫ (subgroupQuotientι A.obj H).left
    rw [Category.assoc, Category.assoc]
    exact congrArg ((W.algClosedPoint w).hom ≫ ·) hab
  obtain ⟨h, hh⟩ := exists_eq_of_map_subgroupQuotientι_eq A.obj H F hq
  have hτ' : (W.algClosedPoint w).hom ≫ a ≫ (h : Aut A.obj).hom.left =
      (W.algClosedPoint w).hom ≫ b := by
    rw [← finiteEtaleFiberFintypeFunctor_map_fiberPointOfComp]
    exact congrArg Subtype.val hh
  have hw : (a ≫ (h : Aut A.obj).hom.left) ≫ (subgroupQuotientι A.obj H).left =
      b ≫ (subgroupQuotientι A.obj H).left := by
    rw [Category.assoc]
    exact (congrArg (a ≫ ·) (congrArg (fun k : A.obj ⟶ subgroupQuotient A.obj H ↦ k.left)
      (hom_comp_subgroupQuotientι A.obj H h))).trans hab
  refine ⟨h, hw, ?_⟩
  have hpt : (W.algClosedPoint w).hom.base default = w :=
    Scheme.algClosedPointHom_apply W w default
  rw [← hpt]
  exact Scheme.Hom.mem_agreeLocus_of_comp_eq _ _ _ hw _ hτ' _

include hS in
/-- **A pointed Galois cover `A` of an irreducible, geometrically unibranch scheme is a Galois
covering of its quotient `A/H` with group `H`.** -/
def PointedGaloisCover.subgroupQuotientCovering :
    EtaleGaloisCovering (subgroupQuotient A.obj H).left H where
  cover := Scheme.Etale.mk (subgroupQuotientι A.obj H).left
  act h := (h : Aut A.obj).hom.left
  act_comp_hom h :=
    congrArg (fun k : A.obj ⟶ subgroupQuotient A.obj H ↦ k.left)
      (hom_comp_subgroupQuotientι A.obj H h)
  act_one := rfl
  act_mul _ _ := rfl
  surjective := surjective_subgroupQuotientι_left A H
  irreducibleSpace := A.irreducibleSpace hS
  exists_mem_agreeLocus a b hab w := exists_mem_agreeLocus_subgroupQuotientι A H a b hab w
  eq_of_comp_eq c _ _ hc := Subtype.ext (aut_eq_of_comp_eq (A := A.obj) c hc)

/-- The total space of the covering `A ⟶ A/H` is the underlying scheme of `A`. -/
@[simp]
theorem PointedGaloisCover.subgroupQuotientCovering_cover_left :
    (A.subgroupQuotientCovering hS H).cover.left = A.obj.left :=
  rfl

/-- The covering `A ⟶ A/H` is connected. -/
instance PointedGaloisCover.connectedSpace_subgroupQuotientCovering_cover :
    ConnectedSpace (A.subgroupQuotientCovering hS H).cover.left :=
  A.connectedSpace

end AlgebraicGeometry

end
