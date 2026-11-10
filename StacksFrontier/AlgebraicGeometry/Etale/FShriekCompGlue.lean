module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompPieceStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompStalk

/-!
# The composition comparison of direct images with compact support

This file assembles the comparison `(f ≫ g)_! ⟶ g_! f_!` of Stacks 0F6T.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section Glue

variable (B : BigEtaleSite.{u}) {S : B.Scheme}

/-- **Gluing a morphism of abelian étale sheaves from its stalks.** Let `aᵢ : Pᵢ ⟶ Q` be a family
of morphisms whose maps on every geometric stalk are jointly epimorphic, and `bᵢ : Pᵢ ⟶ G` a
family of morphisms which on every geometric stalk factor through `aᵢ` by one map `r_s`. Then
there is a morphism `c : Q ⟶ G` with `aᵢ ≫ c = bᵢ`, and its map on stalks is `r_s`. -/
public theorem exists_hom_of_sheafFiber {I : Type (max (u + 1) v)}
    {P : I → Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}}
    {Q G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}}
    (a : ∀ i, P i ⟶ Q) (b : ∀ i, P i ⟶ G)
    (r : ∀ s : GeometricPoint S.obj,
      ((geometricPointSitePoint B S.obj S.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj Q ⟶
        ((geometricPointSitePoint B S.obj S.property s).sheafFiber).obj G)
    (hab : ∀ s i, ((geometricPointSitePoint B S.obj S.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map (a i) ≫ r s =
      ((geometricPointSitePoint B S.obj S.property s).sheafFiber).map (b i))
    (hepi : ∀ (s : GeometricPoint S.obj) (T : AddCommGrpCat.{max (u + 1) v})
      (u₁ u₂ : ((geometricPointSitePoint B S.obj S.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj Q ⟶ T),
      (∀ i, ((geometricPointSitePoint B S.obj S.property s).sheafFiber).map (a i) ≫ u₁ =
        ((geometricPointSitePoint B S.obj S.property s).sheafFiber).map (a i) ≫ u₂) → u₁ = u₂) :
    ∃ c : Q ⟶ G, (∀ i, a i ≫ c = b i) ∧
      ∀ s, ((geometricPointSitePoint B S.obj S.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map c = r s := by
  have hcol : HasColimitsOfShape (Discrete I)
      (Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.instHasColimitsOfShape
  let α : (∐ P) ⟶ Q := Sigma.desc a
  let β : (∐ P) ⟶ G := Sigma.desc b
  have hjf := jointlyFaithful_etaleStalkSheafFiber.{u, v} B S.obj S.property
  have hext : ∀ s {T : AddCommGrpCat.{max (u + 1) v}}
      (u₁ u₂ : ((geometricPointSitePoint B S.obj S.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj (∐ P) ⟶ T),
      (∀ i, ((geometricPointSitePoint B S.obj S.property s).sheafFiber).map (Sigma.ι P i) ≫ u₁ =
        ((geometricPointSitePoint B S.obj S.property s).sheafFiber).map (Sigma.ι P i) ≫ u₂) →
      u₁ = u₂ := by
    intro s T u₁ u₂ h
    exact (isColimitOfPreserves ((geometricPointSitePoint B S.obj S.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})) (colimit.isColimit (Discrete.functor P))).hom_ext
      fun ⟨i⟩ => h i
  have hαi : ∀ i, Sigma.ι P i ≫ α = a i := fun i => Sigma.ι_comp_desc _ _
  have hβi : ∀ i, Sigma.ι P i ≫ β = b i := fun i => Sigma.ι_comp_desc _ _
  have hepiα : ∀ s, Epi (((geometricPointSitePoint B S.obj S.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map α) := by
    intro s
    refine ⟨fun {T} u₁ u₂ h => hepi s T u₁ u₂ fun i => ?_⟩
    rw [← hαi i, Functor.map_comp, Category.assoc, Category.assoc, h]
  have hβs : ∀ s, ((geometricPointSitePoint B S.obj S.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map β =
      ((geometricPointSitePoint B S.obj S.property s).sheafFiber).map α ≫ r s := by
    intro s
    refine hext s _ _ fun i => ?_
    rw [← Functor.map_comp, hβi, ← Category.assoc, ← Functor.map_comp, hαi, hab]
  have : Epi α := hjf.jointlyReflectEpimorphisms.epi α
  have hk : kernel.ι α ≫ β = 0 := by
    refine hjf.map_injective fun s => ?_
    rw [Functor.map_comp, hβs, ← Category.assoc, ← Functor.map_comp, kernel.condition,
      Functor.map_zero, Functor.map_zero, zero_comp]
  refine ⟨Abelian.epiDesc α β hk, fun i => ?_, fun s => ?_⟩
  · rw [← hαi i, Category.assoc, Abelian.comp_epiDesc, hβi]
  · have h := congrArg ((geometricPointSitePoint B S.obj S.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map (Abelian.comp_epiDesc α β hk)
    rw [Functor.map_comp, hβs] at h
    exact (cancel_epi _).1 h

end Glue

section PieceStalk

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  [IsSeparated (B.inclusion.map (jY ≫ g))]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Z.obj)

omit [IsSeparated (B.inclusion.map (jY ≫ g))] [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyQuasiFinite (B.inclusion.map g)] [IsOpenImmersion (B.inclusion.map jX)]
  [IsOpenImmersion (B.inclusion.map jY)] in
include hsq in
/-- Every point of `X` over the image of a point of the geometric fibre of `jY ≫ g` comes from a
point of the geometric fibre of `jX ≫ f ≫ g`, `X'` being the inverse image of `Y'`. -/
public theorem compFiber_induction (y : GeometricFiberPoint B (jY ≫ g) s)
    (x : GeometricFiberPoint B f ((openFiberPoint B jY g s y).toGeometricPoint B g s))
    (P : ∀ y : GeometricFiberPoint B (jY ≫ g) s,
      GeometricFiberPoint B f ((openFiberPoint B jY g s y).toGeometricPoint B g s) → Prop)
    (hP : ∀ x : GeometricFiberPoint B (jX ≫ f ≫ g) s,
      P (compFiberBase B g sq s x) (compFiberTop B g sq s x)) : P y x := by
  have hm : y.1 ≫ B.inclusion.map jY = x.1 ≫ B.inclusion.map f := x.2.symm
  let l := (hsq.map B.inclusion).lift y.1 x.1 hm
  have h2 : l ≫ B.inclusion.map jX = x.1 := (hsq.map B.inclusion).lift_snd _ _ _
  obtain ⟨x'', h1', h2'⟩ : ∃ x'' : GeometricFiberPoint B (jX ≫ f ≫ g) s,
      x''.1 ≫ B.inclusion.map f' = y.1 ∧ x''.1 ≫ B.inclusion.map jX = x.1 := by
    refine ⟨⟨l, ?_⟩, (hsq.map B.inclusion).lift_fst _ _ _, h2⟩
    change l ≫ (B.inclusion.map jX ≫ B.inclusion.map f ≫ B.inclusion.map g) = s.hom
    rw [← Category.assoc, h2, ← Category.assoc, ← hm, Category.assoc]
    exact y.2
  obtain rfl : compFiberBase B g sq s x'' = y := Subtype.ext h1'
  obtain rfl : compFiberTop B g sq s x'' = x := Subtype.ext h2'
  exact hP x''

/-- Two elements of the direct sum of stalks of `f_! F` over the geometric fibre of `g` are equal
if they have the same components through the stalk decompositions of `f_! F`. -/
private theorem fiberStalks_fShriek_ext {Z : B.Scheme} (g : Y ⟶ Z) (s : GeometricPoint Z.obj)
    (a b : fiberStalks.{u, max (u + 1) v} B g s ((fShriekFunctor.{u, v} B f).obj F))
    (h : ∀ (y : GeometricFiberPoint B g s) (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)),
      ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        ((a : fiberStalks.{u, max (u + 1) v} B g s _) y) :
          fiberStalks.{u, max (u + 1) v} B f _ F) x =
      ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        ((b : fiberStalks.{u, max (u + 1) v} B g s _) y) :
          fiberStalks.{u, max (u + 1) v} B f _ F) x) : a = b := by
  refine DFinsupp.ext fun y => ?_
  refine (AddCommGrpCat.mono_iff_injective
    (fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom).1 inferInstance ?_
  exact DFinsupp.ext fun x => h y x

/-- **The piece of the composition comparison is the regrouping of the geometric fibre**, read
through the covariance of Stacks 0F6S. -/
public theorem compFiberStalksMap_openCovarianceFiberStalksMap
    (ξ : fiberStalks.{u, max (u + 1) v} B (jX ≫ f ≫ g) s ((openRestriction.{u, v} B jX).obj F)) :
    compFiberStalksMap B f g s F (openCovarianceFiberStalksMap B jX (f ≫ g) F s ξ) =
      compPieceFiberStalksMap B g sq hsq F s ξ := by
  refine fiberStalks_fShriek_ext B _ g _ _ _ fun y x => ?_
  rw [compFiberStalksMap_apply]
  by_cases hy : ∃ y' : GeometricFiberPoint B (jY ≫ g) s, openFiberPoint B jY g s y' = y
  · obtain ⟨y', rfl⟩ := hy
    refine compFiber_induction B g sq hsq s y' x (fun y' x =>
      (openCovarianceFiberStalksMap B jX (f ≫ g) F s ξ :
        fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F)
          (compFiberPointOf B f g s (openFiberPoint B jY g s y') x) =
        ((fShriekStalkIso.{u, v} B f ((openFiberPoint B jY g s y').toGeometricPoint B g s) F).hom
          ((compPieceFiberStalksMap B g sq hsq F s ξ : fiberStalks.{u, max (u + 1) v} B g s _)
            (openFiberPoint B jY g s y')) : fiberStalks.{u, max (u + 1) v} B f _ F) x)
      fun x'' => ?_
    exact (openCovarianceFiberStalksMap_apply B jX (f ≫ g) F s ξ x'').trans
      (compPieceFiberStalksMap_apply B g sq hsq F s ξ x'').symm
  · rw [compPieceFiberStalksMap_apply_eq_zero B g sq hsq F s ξ y fun y' hy' => hy ⟨y', hy'⟩,
      map_zero, DirectSum.zero_apply]
    refine openCovarianceFiberStalksMap_apply_eq_zero B jX (f ≫ g) F s ξ _ fun x'' hx => hy ?_
    refine ⟨compFiberBase B g sq s x'', ?_⟩
    rw [← compFiberPoint_compFiberPointOf B f g s y x, ← hx]
    refine Subtype.ext ?_
    change (x''.1 ≫ B.inclusion.map f') ≫ B.inclusion.map jY =
      (x''.1 ≫ B.inclusion.map jX) ≫ B.inclusion.map f
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, sq]

end PieceStalk

section Cover

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The inverse image in `X` of an open of `Y`. -/
public abbrev compCoverOpen (V : (B.inclusion.obj Y).Opens) : (B.inclusion.obj X).Opens :=
  (B.inclusion.map f) ⁻¹ᵁ V

/-- The restriction of `f` to the inverse image of an open of `Y`. -/
public def compCoverRestrict (V : (B.inclusion.obj Y).Opens) :
    OpenCoverShriek.openScheme B (compCoverOpen B f V) ⟶ OpenCoverShriek.openScheme B V :=
  ObjectProperty.homMk ((B.inclusion.map f) ∣_ V)

/-- The restriction of `f` to the inverse image of `V` commutes with `f` and the inclusions of
the two opens. -/
public theorem compCoverRestrict_sq (V : (B.inclusion.obj Y).Opens) :
    compCoverRestrict B f V ≫ OpenCoverShriek.openSchemeι B V =
      OpenCoverShriek.openSchemeι B (compCoverOpen B f V) ≫ f :=
  ObjectProperty.hom_ext _ (morphismRestrict_ι _ _)

/-- The inverse image of an open is the fibre product. -/
public theorem isPullback_compCoverRestrict (V : (B.inclusion.obj Y).Opens) :
    IsPullback (compCoverRestrict B f V) (OpenCoverShriek.openSchemeι B (compCoverOpen B f V))
      (OpenCoverShriek.openSchemeι B V) f :=
  IsPullback.of_map B.inclusion (compCoverRestrict_sq B f V)
    (isPullback_morphismRestrict (B.inclusion.map f) V)

/-- An affine open of `Y` is separated over anything. -/
public theorem isSeparated_compCover {Z : B.Scheme} (g : Y ⟶ Z) (V : (B.inclusion.obj Y).Opens)
    (hV : IsAffineOpen V) :
    IsSeparated (B.inclusion.map (OpenCoverShriek.openSchemeι B V ≫ g)) := by
  have : AlgebraicGeometry.IsAffine (V : Scheme.{u}) := hV
  change IsSeparated (V.ι ≫ B.inclusion.map g)
  infer_instance

end Cover

section Comparison

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The affine opens of `Y`, the index of the covering of `X` the comparison is glued over. -/
public abbrev CompCoverIndex :=
  ULift.{max (u + 1) v} {V : (B.inclusion.obj Y).Opens // IsAffineOpen V}

/-- The piece of the comparison on the inverse image of an affine open of `Y`. -/
public def compCoverPiece (i : CompCoverIndex.{u, v} B (Y := Y)) :
    (openShriekPushforward.{u, v} B (OpenCoverShriek.openSchemeι B (compCoverOpen B f i.down.1))
        (f ≫ g)).obj F ⟶
      (fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F) :=
  haveI := isSeparated_compCover B g i.down.1 i.down.2
  compPieceMap B g (compCoverRestrict_sq B f i.down.1) (isPullback_compCoverRestrict B f i.down.1) F

/-- **The stalk behaviour of the comparison of Stacks 0F6T**: on the stalk decompositions of
Stacks 0F5F at every geometric point of `Z`, a morphism `(f ≫ g)_! F ⟶ g_!(f_! F)` is the
regrouping of the geometric fibre of `f ≫ g`. -/
public def HasCompShriekStalks
    (c : (fShriekFunctor.{u, v} B (f ≫ g)).obj F ⟶
      (fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F)) : Prop :=
  ∀ s : GeometricPoint Z.obj,
    ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map c =
      (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom ≫
        AddCommGrpCat.ofHom (compFiberStalksMap B f g s F) ≫
        (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).inv

/-- The covariance maps of the inverse images of the affine opens of `Y` are jointly epimorphic
on every geometric stalk. -/
public theorem compCover_jointlyEpi (s : GeometricPoint Z.obj) (T : AddCommGrpCat.{max (u + 1) v})
    (u₁ u₂ : ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).obj ((fShriekFunctor.{u, v} B (f ≫ g)).obj F) ⟶ T)
    (h : ∀ i : CompCoverIndex.{u, v} B (Y := Y),
      ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber).map
          ((openCovarianceShriekMap.{u, v} B
            (OpenCoverShriek.openSchemeι B (compCoverOpen B f i.down.1)) (f ≫ g)).app F) ≫ u₁ =
        ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber).map
          ((openCovarianceShriekMap.{u, v} B
            (OpenCoverShriek.openSchemeι B (compCoverOpen B f i.down.1)) (f ≫ g)).app F) ≫ u₂) :
    u₁ = u₂ := by
  classical
  refine (cancel_epi (fShriekStalkIso.{u, v} B (f ≫ g) s F).inv).1 ?_
  refine AddCommGrpCat.hom_ext (DirectSum.addHom_ext fun x b => ?_)
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show (x.1 ≫ B.inclusion.map f).base default ∈ (⊤ : (B.inclusion.obj Y).Opens) from trivial)
  let i : CompCoverIndex.{u, v} B (Y := Y) := ⟨⟨V, hV⟩⟩
  obtain ⟨x', rfl⟩ := OpenCoverShriek.exists_openFiberPoint_of_mem_opens B (f ≫ g) s
    (compCoverOpen B f V) x hyV
  let j := OpenCoverShriek.openSchemeι B (compCoverOpen B f V)
  let z := ((fShriekStalkIso.{u, v} B (j ≫ f ≫ g) s ((openRestriction.{u, v} B j).obj F)).inv
    (DirectSum.of _ x' ((openFiberStalkIso.{u, v} B j (f ≫ g) F s x').inv b)))
  have hc : (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom
      (((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B j (f ≫ g)).app F) z) =
      DirectSum.of (fun x : GeometricFiberPoint B (f ≫ g) s =>
        ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s) F.obj))
        (openFiberPoint B j (f ≫ g) s x') b := by
    refine (ConcreteCategory.congr_hom
      (ofHom_of_comp_fShriekStalkIso_openCovariance.{u, v} B j (f ≫ g) F s x')
      ((openFiberStalkIso.{u, v} B j (f ≫ g) F s x').inv b)).trans ?_
    exact congrArg (DirectSum.of (fun x : GeometricFiberPoint B (f ≫ g) s =>
        ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s) F.obj))
      (openFiberPoint B j (f ≫ g) s x'))
      (Iso.inv_hom_id_apply (openFiberStalkIso.{u, v} B j (f ≫ g) F s x') b)
  have hz : (fShriekStalkIso.{u, v} B (f ≫ g) s F).inv (DirectSum.of _ _ b) =
      ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B j (f ≫ g)).app F) z := by
    rw [← hc]
    exact Iso.hom_inv_id_apply _ _
  change u₁ ((fShriekStalkIso.{u, v} B (f ≫ g) s F).inv (DirectSum.of _ _ b)) =
    u₂ ((fShriekStalkIso.{u, v} B (f ≫ g) s F).inv (DirectSum.of _ _ b))
  rw [hz]
  exact ConcreteCategory.congr_hom (h i) z

/-- **Existence of the comparison of Stacks 0F6T.** There is a morphism
`(f ≫ g)_! F ⟶ g_!(f_! F)` which on the stalk decompositions of Stacks 0F5F at every geometric
point is the regrouping of the geometric fibre of `f ≫ g`. It is glued from its pieces on the
inverse images of the affine opens of `Y`. -/
public theorem exists_hasCompShriekStalks :
    ∃ c : (fShriekFunctor.{u, v} B (f ≫ g)).obj F ⟶
        (fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F),
      HasCompShriekStalks B f g F c := by
  obtain ⟨c, -, hc⟩ := exists_hom_of_sheafFiber B (I := CompCoverIndex.{u, v} B (Y := Y))
    (fun i => (openCovarianceShriekMap.{u, v} B
      (OpenCoverShriek.openSchemeι B (compCoverOpen B f i.down.1)) (f ≫ g)).app F)
    (fun i => compCoverPiece B f g F i)
    (fun s => (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom ≫
      AddCommGrpCat.ofHom (compFiberStalksMap B f g s F) ≫
      (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).inv)
    (fun s i => by
      have := isSeparated_compCover B g i.down.1 i.down.2
      refine (cancel_epi (fShriekStalkIso.{u, v} B
        (OpenCoverShriek.openSchemeι B (compCoverOpen B f i.down.1) ≫ f ≫ g) s
        ((openRestriction.{u, v} B
          (OpenCoverShriek.openSchemeι B (compCoverOpen B f i.down.1))).obj F)).inv).1 ?_
      refine (cancel_mono (fShriekStalkIso.{u, v} B g s
        ((fShriekFunctor.{u, v} B f).obj F)).hom).1 ?_
      refine ConcreteCategory.hom_ext _ _ fun ξ => ?_
      exact (Iso.inv_hom_id_apply (fShriekStalkIso.{u, v} B g s
        ((fShriekFunctor.{u, v} B f).obj F)) _).trans
        (compFiberStalksMap_openCovarianceFiberStalksMap B g (compCoverRestrict_sq B f i.down.1)
          (isPullback_compCoverRestrict B f i.down.1) F s ξ))
    (compCover_jointlyEpi B f g F)
  exact ⟨c, hc⟩

/-- **The comparison `(f ≫ g)_! F ⟶ g_!(f_! F)` of Stacks 0F6T**, the morphism whose effect on
the stalk decompositions of Stacks 0F5F is the regrouping of the geometric fibre of `f ≫ g`. -/
public def compShriekMap :
    (fShriekFunctor.{u, v} B (f ≫ g)).obj F ⟶
      (fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F) :=
  (exists_hasCompShriekStalks B f g F).choose

/-- The comparison `compShriekMap` has the stalk behaviour of Stacks 0F6T. -/
public theorem compShriekMap_hasCompShriekStalks :
    HasCompShriekStalks B f g F (compShriekMap B f g F) :=
  (exists_hasCompShriekStalks B f g F).choose_spec

/-- The comparison is the only morphism with its stalk behaviour. -/
public theorem eq_compShriekMap
    {c : (fShriekFunctor.{u, v} B (f ≫ g)).obj F ⟶
      (fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F)}
    (hc : HasCompShriekStalks B f g F c) : c = compShriekMap B f g F :=
  (jointlyFaithful_etaleStalkSheafFiber.{u, v} B Z.obj Z.property).map_injective fun s =>
    (hc s).trans (compShriekMap_hasCompShriekStalks B f g F s).symm

variable {F} in
omit [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)] in
/-- The regrouping of the geometric fibre is natural in the abelian sheaf. -/
public theorem compFiberStalksMap_natural (s : GeometricPoint Z.obj)
    {F' : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ F') (ξ : fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F) :
    compFiberStalksMap B f g s F' (fiberStalksMap.{u, max (u + 1) v} B (f ≫ g) s φ ξ) =
      fiberStalksMap.{u, max (u + 1) v} B g s ((fShriekFunctor.{u, v} B f).map φ)
        (compFiberStalksMap B f g s F ξ) := by
  refine fiberStalks_fShriek_ext B _ g _ _ _ fun y x => ?_
  rw [compFiberStalksMap_apply]
  have hn : (fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F').hom
      ((fiberStalksMap.{u, max (u + 1) v} B g s ((fShriekFunctor.{u, v} B f).map φ)
        (compFiberStalksMap B f g s F ξ) : fiberStalks.{u, max (u + 1) v} B g s _) y) =
      fiberStalksMap.{u, max (u + 1) v} B f (y.toGeometricPoint B g s) φ
        ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
          ((compFiberStalksMap B f g s F ξ : fiberStalks.{u, max (u + 1) v} B g s _) y)) :=
    ConcreteCategory.congr_hom
      (fShriekStalkIso_natural.{u, v} B f (y.toGeometricPoint B g s) φ) _
  rw [hn]
  change (colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B X.obj
      X.property ((compFiberPointOf B f g s y x).toGeometricPoint B (f ≫ g) s))).op φ.1)).hom
      (ξ (compFiberPointOf B f g s y x)) =
    (colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B X.obj
      X.property (x.toGeometricPoint B f (y.toGeometricPoint B g s)))).op φ.1)).hom
      (((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
          ((compFiberStalksMap B f g s F ξ : fiberStalks.{u, max (u + 1) v} B g s _) y) :
        fiberStalks.{u, max (u + 1) v} B f _ F) x)
  rw [compFiberStalksMap_apply]
  rfl

/-- **The comparison is natural in the abelian sheaf.** -/
public theorem compShriekMap_naturality
    {F' : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ F') :
    (fShriekFunctor.{u, v} B (f ≫ g)).map φ ≫ compShriekMap B f g F' =
      compShriekMap B f g F ≫
        (fShriekFunctor.{u, v} B g).map ((fShriekFunctor.{u, v} B f).map φ) := by
  refine (jointlyFaithful_etaleStalkSheafFiber.{u, v} B Z.obj Z.property).map_injective fun s => ?_
  rw [Functor.map_comp, Functor.map_comp, compShriekMap_hasCompShriekStalks,
    compShriekMap_hasCompShriekStalks]
  have h1 : ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map ((fShriekFunctor.{u, v} B (f ≫ g)).map φ) ≫
      (fShriekStalkIso.{u, v} B (f ≫ g) s F').hom =
      (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom ≫
        AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B (f ≫ g) s φ) :=
    fShriekStalkIso_natural.{u, v} B (f ≫ g) s φ
  have h2 : ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
        ((fShriekFunctor.{u, v} B g).map ((fShriekFunctor.{u, v} B f).map φ)) ≫
      (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F')).hom =
      (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).hom ≫
        AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B g s
          ((fShriekFunctor.{u, v} B f).map φ)) :=
    fShriekStalkIso_natural.{u, v} B g s ((fShriekFunctor.{u, v} B f).map φ)
  have h2' : (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).inv ≫
      ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
        ((fShriekFunctor.{u, v} B g).map ((fShriekFunctor.{u, v} B f).map φ)) =
      AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B g s
          ((fShriekFunctor.{u, v} B f).map φ)) ≫
        (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F')).inv :=
    (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 h2).trans (Category.assoc _ _ _))
  have hR : AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B (f ≫ g) s φ) ≫
      AddCommGrpCat.ofHom (compFiberStalksMap B f g s F') =
      AddCommGrpCat.ofHom (compFiberStalksMap B f g s F) ≫
        AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B g s
          ((fShriekFunctor.{u, v} B f).map φ)) :=
    ConcreteCategory.hom_ext _ _ fun ξ => compFiberStalksMap_natural B f g s φ ξ
  exact (((reassoc_of% h1) _).trans (Category.assoc _ _ _)).trans
    ((congrArg ((fShriekStalkIso.{u, v} B (f ≫ g) s F).hom ≫ ·) ((reassoc_of% hR) _)).trans
      (congrArg (fun k => (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom ≫
          AddCommGrpCat.ofHom (compFiberStalksMap B f g s F) ≫ k) h2'.symm))

end Comparison

end AlgebraicGeometry.SmallEtale

end
