module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantSheaf

/-!
# The constant group sheaf and the constant group scheme

Let `G` be an abstract group and let `S` be a scheme. The constant sheaf of *groups* with value
`G` on a site over `S` is the group-valued functor of points of the constant group scheme
`G_S`, and the identification is pinned down by its action on the constant sections of the
constant presheaf. `AlgebraicGeometry.GroupSheafRepresentation` packages that data, and this
file produces it for every Grothendieck topology on the schemes over `S` between the Zariski
and the fpqc topology.

## Main definitions

* `AlgebraicGeometry.GroupSheafRepresentation` — a sheafification of the constant presheaf of
  groups, together with an isomorphism onto the restricted group-valued functor of points of
  `G_S` and the compatibility of that isomorphism with the constant sections.
* `AlgebraicGeometry.constantToLocallyConstantMapsOnGrp` — the canonical map of presheaves of
  groups from the constant presheaf to the locally constant maps.

## Main results

* `AlgebraicGeometry.constantGroupSheafIsoLocallyConstantMapsOnGrp` identifies the constant
  sheaf of groups along a functor `H` to the schemes over `S` with the presheaf of locally
  constant maps, and `constantGroupSheafIsoLocallyConstantMapsOnGrp_unit` fixes that
  identification on constant sections.
* `AlgebraicGeometry.groupSheafRepresentationOfLocallyConstantMaps` assembles a
  `GroupSheafRepresentation` from the covering data of `H`.
* `AlgebraicGeometry.overSchemeOpenCoverData`: every open cover of the underlying scheme of an
  object of the schemes over `S` is refined by a covering family for any topology finer than
  the Zariski topology.
* `AlgebraicGeometry.constantGroupSheafRepresentedByConstantGroupScheme` is the representation
  on the schemes over `S` for every topology between the Zariski and the fpqc topology.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

add_to_stacks 03P5 "representation by the constant group scheme"
  AlgebraicGeometry.constantGroupSchemePointsIsoLocallyConstantMaps

/-- A representation of the constant sheaf of groups with value `G` by the constant group scheme
`G_S` along `H`: a weak sheafification of presheaves of groups for `J`, an isomorphism of
presheaves of groups from the constant sheaf to the group-valued functor of points of `G_S`
composed with `H`, and the condition that this isomorphism sends the image of each `g : G` under
the sheafification unit to the constant map with value `g`. -/
public def GroupSheafRepresentation {C : Type (u + 1)} [Category.{u} C] (S : Scheme.{u})
    (H : C ⥤ Over S) (J : GrothendieckTopology C) (G : Type (max (u + 1) v)) [Small.{u} G]
    [Group G] : Type _ :=
  Σ' h : HasWeakSheafify J GrpCat.{max (u + 1) v},
    letI := h
    Σ' e : ((constantSheaf J GrpCat.{max (u + 1) v}).obj (GrpCat.of G)).obj ≅
      H.op ⋙ (yonedaGrp.obj (constantGroupScheme G S) ⋙
        GrpCat.uliftFunctor.{max (u + 1) v}),
      ∀ (T : Cᵒᵖ) (g : G),
        ((constantGroupSchemePointsIsoLocallyConstantMaps G S).hom.app (H.op.obj T))
          ((e.hom.app T)
            ((toSheafify J ((Functor.const Cᵒᵖ).obj (GrpCat.of G))).app T g)) =
          LocallyConstant.const (H.obj T.unop).left g

/-- The map of presheaves of groups sending `g : G` to the constant map with value `g`, from
the constant presheaf on a site `C` to the locally constant maps on the schemes `H.obj T`. -/
public def constantToLocallyConstantMapsOnGrp {C : Type (u + 1)} [Category.{u} C]
    (S : Scheme.{u}) (H : C ⥤ Over S) (G : Type (max (u + 1) v)) [Group G] :
    (Functor.const Cᵒᵖ).obj (GrpCat.of G) ⟶ H.op ⋙ locallyConstantMapsOver G S where
  app T := GrpCat.ofHom (LocallyConstant.constMonoidHom (X := (H.obj T.unop).left))
  naturality X Y f := by
    ext g
    rfl

/-- The constant sheaf of groups along a functor `H` to the schemes over `S` is the presheaf of
locally constant maps, as soon as every open cover of the underlying scheme of `H.obj T` is
refined by a `J`-covering family of `T`, the empty sieve covers every `T` with `H.obj T` empty,
and the underlying presheaf of sets of locally constant maps is a `J`-sheaf. -/
public def constantGroupSheafIsoLocallyConstantMapsOnGrp {C : Type (u + 1)} [Category.{u} C]
    (S : Scheme.{u}) (H : C ⥤ Over S) (G : Type (max (u + 1) v)) [Group G]
    (J : GrothendieckTopology C) [HasWeakSheafify J GrpCat.{max (u + 1) v}]
    [J.WEqualsLocallyBijective GrpCat.{max (u + 1) v}]
    (hOpen : ∀ {T : C} (U : (H ⋙ Over.forget S).obj T →
      ((H ⋙ Over.forget S).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T)
        (r : I → (H ⋙ Over.forget S).obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, (H ⋙ Over.forget S).map (a i) y ∈ U (r i))
    (hEmpty : ∀ {T : C}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T)
    (hF : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat)) :
    ((constantSheaf J GrpCat.{max (u + 1) v}).obj (GrpCat.of G)).obj ≅
      H.op ⋙ locallyConstantMapsOver G S := by
  let α := constantToLocallyConstantMapsOnGrp S H G
  let hP : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S) :=
    Presheaf.isSheaf_of_isSheaf_comp J (H.op ⋙ locallyConstantMapsOver G S)
      (forget GrpCat) hF
  have hUnder : Functor.whiskerRight α (forget GrpCat) =
      constantToLocallyConstantMapsOn (H ⋙ Over.forget S) G := by
    ext T g
    exact LocallyConstant.ext fun _ => rfl
  let : Presheaf.IsLocallyInjective J α := by
    apply (Presheaf.isLocallyInjective_forget_iff J α).1
    rw [hUnder]
    exact constantToLocallyConstantMapsOn_isLocallyInjective (H ⋙ Over.forget S) G J hEmpty
  let : Presheaf.IsLocallySurjective J α := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget J α).2
    rw [hUnder]
    exact constantToLocallyConstantMapsOn_isLocallySurjective (H ⋙ Over.forget S) G J hOpen
  have hα : IsIso ((presheafToSheaf J GrpCat.{max (u + 1) v}).map α) := by
    rw [← J.W_iff]
    exact (J.W_iff_isLocallyBijective α).mpr ⟨inferInstance, inferInstance⟩
  let P := (Functor.const Cᵒᵖ).obj (GrpCat.of G)
  let L : Sheaf J GrpCat.{max (u + 1) v} := ⟨_, hP⟩
  let e₁ : (constantSheaf J GrpCat.{max (u + 1) v}).obj (GrpCat.of G) ≅
      (presheafToSheaf J GrpCat.{max (u + 1) v}).obj P := Iso.refl _
  let e₂ : (presheafToSheaf J GrpCat.{max (u + 1) v}).obj P ≅
      (presheafToSheaf J GrpCat.{max (u + 1) v}).obj
        (H.op ⋙ locallyConstantMapsOver G S) :=
    asIso ((presheafToSheaf J GrpCat.{max (u + 1) v}).map α)
  let e₃ : (presheafToSheaf J GrpCat.{max (u + 1) v}).obj
      (H.op ⋙ locallyConstantMapsOver G S) ≅ L :=
    asIso ((sheafificationAdjunction J GrpCat.{max (u + 1) v}).counit.app L)
  simpa [P, L, α] using (Functor.mapIso (sheafToPresheaf J GrpCat.{max (u + 1) v})
    ((e₁.trans e₂).trans e₃))

/-- The identification of the constant sheaf of groups with locally constant maps sends the
sheafification-unit image of `g` to the constant map with value `g`. -/
public theorem constantGroupSheafIsoLocallyConstantMapsOnGrp_unit {C : Type (u + 1)}
    [Category.{u} C] (S : Scheme.{u}) (H : C ⥤ Over S) (G : Type (max (u + 1) v)) [Group G]
    (J : GrothendieckTopology C) [HasWeakSheafify J GrpCat.{max (u + 1) v}]
    [J.WEqualsLocallyBijective GrpCat.{max (u + 1) v}]
    (hOpen : ∀ {T : C} (U : (H ⋙ Over.forget S).obj T →
      ((H ⋙ Over.forget S).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T)
        (r : I → (H ⋙ Over.forget S).obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, (H ⋙ Over.forget S).map (a i) y ∈ U (r i))
    (hEmpty : ∀ {T : C}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T)
    (hF : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat))
    (T : Cᵒᵖ) (g : G) :
    ((constantGroupSheafIsoLocallyConstantMapsOnGrp S H G J hOpen hEmpty hF).hom.app T)
      (((toSheafify J ((Functor.const Cᵒᵖ).obj (GrpCat.of G))).app T) g) =
      LocallyConstant.const (H.obj T.unop).left g := by
  let α := constantToLocallyConstantMapsOnGrp S H G
  have hP : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S) :=
    Presheaf.isSheaf_of_isSheaf_comp J (H.op ⋙ locallyConstantMapsOver G S)
      (forget GrpCat) hF
  change (sheafifyLift J α hP).app T
    (((toSheafify J ((Functor.const Cᵒᵖ).obj (GrpCat.of G))).app T) g) = _
  exact congrArg (fun f => f.app T g) (toSheafify_sheafifyLift J α hP)

/-- The representation of the constant group sheaf along `H` by the constant group scheme,
under the hypotheses of `AlgebraicGeometry.constantGroupSheafIsoLocallyConstantMapsOnGrp`. -/
public def groupSheafRepresentationOfLocallyConstantMaps {C : Type (u + 1)} [Category.{u} C]
    (S : Scheme.{u}) (H : C ⥤ Over S) (J : GrothendieckTopology C)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G]
    [HasWeakSheafify J GrpCat.{max (u + 1) v}]
    [J.WEqualsLocallyBijective GrpCat.{max (u + 1) v}]
    (hOpen : ∀ {T : C} (U : (H ⋙ Over.forget S).obj T →
      ((H ⋙ Over.forget S).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T)
        (r : I → (H ⋙ Over.forget S).obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, (H ⋙ Over.forget S).map (a i) y ∈ U (r i))
    (hEmpty : ∀ {T : C}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T)
    (hF : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat)) :
    GroupSheafRepresentation S H J G := by
  refine ⟨inferInstance,
    (constantGroupSheafIsoLocallyConstantMapsOnGrp S H G J hOpen hEmpty hF).trans
    (Functor.isoWhiskerLeft H.op (constantGroupSchemePointsIsoLocallyConstantMaps G S).symm),
    fun T g => ?_⟩
  change ((constantGroupSchemePointsIsoLocallyConstantMaps G S).hom.app (H.op.obj T))
      (((constantGroupSchemePointsIsoLocallyConstantMaps G S).inv.app (H.op.obj T))
        ((constantGroupSheafIsoLocallyConstantMapsOnGrp S H G J hOpen hEmpty hF).hom.app T
          (((toSheafify J ((Functor.const Cᵒᵖ).obj (GrpCat.of G))).app T) g))) = _
  rw [constantGroupSheafIsoLocallyConstantMapsOnGrp_unit S H G J hOpen hEmpty hF T g]
  exact ConcreteCategory.congr_hom
    ((constantGroupSchemePointsIsoLocallyConstantMaps G S).inv_hom_id_app (H.op.obj T)) _

/-- The representation of the constant group sheaf along `H` by the constant group scheme, as
soon as every open cover of the underlying scheme of `H.obj T` is refined by a `J`-covering
family of `T` and the underlying presheaf of sets of locally constant maps is a `J`-sheaf. -/
public def groupSheafRepresentationOfLocallyConstantMaps_of_underlyingSheaf
    {C : Type (u + 1)} [Category.{u} C] (S : Scheme.{u}) (H : C ⥤ Over S)
    (J : GrothendieckTopology C) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G]
    [HasWeakSheafify J GrpCat.{max (u + 1) v}]
    [J.WEqualsLocallyBijective GrpCat.{max (u + 1) v}]
    (hOpen : ∀ {T : C} (U : (H ⋙ Over.forget S).obj T →
      ((H ⋙ Over.forget S).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T)
        (r : I → (H ⋙ Over.forget S).obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, (H ⋙ Over.forget S).map (a i) y ∈ U (r i))
    (hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat)) :
    GroupSheafRepresentation S H J G := by
  have hEmpty : ∀ {T : C}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T :=
    fun hT => openCoverData_bottom (H ⋙ Over.forget S) J hOpen hT
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen hEmpty hSet

/-- Every open cover of the underlying scheme of an object of the schemes over `S` is refined
by a covering family for any topology finer than the Zariski topology. -/
public theorem overSchemeOpenCoverData (S : Scheme.{u}) (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J) :
    ∀ {T : Over S} (U : T.left → T.left.Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → Over S) (a : ∀ i, W i ⟶ T) (r : I → T.left),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, (a i).left y ∈ U (r i) := by
  intro T U hU
  let I := ULift.{u + 1, u} T.left
  let V : I → T.left.Opens := fun x => U x.down
  let O : T.left.OpenCover.{u + 1} :=
    T.left.openCoverOfIsOpenCover V ((ULift.down_surjective.iSup_comp U).trans hU)
  let W : I → Over S := fun x => Over.mk (O.f x ≫ T.hom)
  let a : ∀ x, W x ⟶ T := fun x => Over.homMk (O.f x) (by simp [W])
  have hcoverZ : Sieve.ofArrows W a ∈ Scheme.zariskiTopology.over S T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows O.X O.f ∈ Scheme.zariskiTopology T.left
    exact O.mem_grothendieckTopology
  exact ⟨I, W, a, ULift.down, hZ _ hcoverZ, fun _ y => y.property⟩

/-- The constant sheaf of groups on the schemes over `S` is represented by the constant group
scheme `G_S`, compatibly with the constant-presheaf unit, for every topology between the
Zariski and the fpqc topology. -/
@[stacks 03P5 "group-valued representation on the big over-site"]
public def constantGroupSheafRepresentedByConstantGroupScheme (S : Scheme.{u})
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J) (hF : J ≤ Scheme.fpqcTopology.over S) :
    GroupSheafRepresentation S (𝟭 (Over S)) J G := by
  let H : Over S ⥤ Over S := 𝟭 (Over S)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen : ∀ {T : Over S} (U : T.left → T.left.Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → Over S) (a : ∀ i, W i ⟶ T) (r : I → T.left),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, (a i).left y ∈ U (r i) :=
    overSchemeOpenCoverData S J hZ
  have hEmpty : ∀ {T : Over S}, IsEmpty T.left → (⊥ : Sieve T) ∈ J T :=
    fun hT => openCoverData_bottom (Over.forget S) J hOpen hT
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen hEmpty
    ((Presheaf.isSheaf_of_iso_iff (relativeLocallyConstantMapsIsoOnScheme S H G)).mpr
      ((locallyConstantMapsOver_isSheaf_fpqc S G).of_le hF))

end AlgebraicGeometry

end
