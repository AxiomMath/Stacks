module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.QcqsInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactZariskiLocalTarget
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension

/-!
# Elementary distinguished squares enlarging an open subspace

Auxiliary material for **Stacks 09IT**: the points of the members of an elementary
distinguished square, the enlargement of an open subspace along such a square, and the
transport of a square inside an open subspace to the ambient algebraic space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
local instance (priority := high) {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W) (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

/-! ### Enlarging a quasi-compact open subspace

The induction principle of Stacks 09IT: a property of the quasi-compact open subspaces of a
quasi-compact quasi-separated algebraic space `X` which holds for a fixed quasi-compact open
subspace `W` and is inherited across elementary distinguished squares of quasi-compact open
subspaces containing `W` with affine étale member holds for `X`.
-/

/-- The identity is an open immersion. -/
theorem isOpenImmersion_id (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsOpenImmersion B S hS (𝟙 F) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda (𝟙 F), ?_⟩
  intro A A' g f f' hpb
  have hMapIso : IsIso (yoneda.map f') := hpb.isIso_snd_of_isIso
  let : IsIso (yoneda.map f') := hMapIso
  have hIso : IsIso f' :=
    Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful f'
  let : IsIso f' := hIso
  change AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map f')
  infer_instance

/-- Every open set of points of an algebraic space is the point set of an open subspace. -/
private theorem exists_openSubspace_of_isOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (T : Set (points B S hS F)) (hT : @IsOpen _ (pointTopology B S hS F) T) :
    ∃ (G : Subfunctor F) (_hG : IsOpenSubspace B S hS G),
      Set.range (pointsMap B S hS G.toFunctor G.ι) = T := by
  let : TopologicalSpace (points B S hS F) := pointTopology B S hS F
  refine ⟨((openSubspacesOrderIso B S hS F hF).symm ⟨T, hT⟩).1,
    ((openSubspacesOrderIso B S hS F hF).symm ⟨T, hT⟩).2, ?_⟩
  rw [← openSubspacesOrderIso_apply B S hS F hF
    ((openSubspacesOrderIso B S hS F hF).symm ⟨T, hT⟩)]
  simp

/-- The point set of the range of a monomorphism, followed by a further morphism, is the
point set of that composite. -/
private theorem range_pointsMap_range_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G) [Mono k] (h : G ⟶ H) :
    Set.range (pointsMap B S hS (Subfunctor.range k).toFunctor
        ((Subfunctor.range k).ι ≫ h)) =
      Set.range (pointsMap B S hS F (k ≫ h)) := by
  have hsurj : Set.range (pointsMap B S hS F (Subfunctor.toRange k)) = Set.univ :=
    (pointsMap_surjective_of_isIso B S hS (Subfunctor.toRange k)).range_eq
  conv_rhs => rw [← Subfunctor.toRange_ι k, Category.assoc, pointsMap_comp,
    Set.range_comp]
  rw [hsurj, Set.image_univ]

/-- The point set of the range of a monomorphism is the point set of that monomorphism. -/
alias range_pointsMap_range := range_pointsMap_ι_subfunctorRange

/-- A monomorphism whose range is an open subspace is étale. -/
private theorem isEtale_of_isOpenSubspace_range
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G) [Mono k]
    (hR : IsOpenSubspace B S hS (Subfunctor.range k)) :
    IsEtale B S hS k := by
  have h1 : IsEtale B S hS (Subfunctor.toRange k) :=
    etale_of_iso_presheaves B S hS (asIso (Subfunctor.toRange k))
  have h2 : IsEtale B S hS (Subfunctor.range k).ι :=
    etale_of_openImmersion B S hS (Subfunctor.range k).ι hR.2
  simpa only [Subfunctor.toRange_ι] using isEtale_comp B S hS h1 h2

/-- The point set of a subspace pulled back along an isomorphism of the ambient presheaf,
measured in a further target, is the point set of the subspace itself. -/
private theorem range_pointsMap_preimage_isoHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) (C : Subfunctor G)
    (h : G ⟶ H) :
    Set.range (pointsMap B S hS (C.preimage e.hom).toFunctor
        ((C.preimage e.hom).ι ≫ (e.hom ≫ h))) =
      Set.range (pointsMap B S hS C.toFunctor (C.ι ≫ h)) := by
  have hiso : IsIso (C.fromPreimage e.hom) := fromPreimage_isIso_of_isIso C e
  have hsurj : Set.range (pointsMap B S hS (C.preimage e.hom).toFunctor
      (C.fromPreimage e.hom)) = Set.univ :=
    (pointsMap_surjective_of_isIso B S hS (C.fromPreimage e.hom)).range_eq
  have hfac : (C.preimage e.hom).ι ≫ (e.hom ≫ h) =
      C.fromPreimage e.hom ≫ (C.ι ≫ h) := by
    rw [← Category.assoc, ← Subfunctor.fromPreimage_ι, Category.assoc]
  rw [hfac, pointsMap_comp, Set.range_comp, hsurj, Set.image_univ]

private theorem open_le_of_points
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (U V : Subfunctor X)
    (hU : IsOpenSubspace B S hS U)
    (hV : IsOpenSubspace B S hS V)
    (hpoints : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (pointsMap B S hS V.toFunctor V.ι)) : U ≤ V := by
  let : TopologicalSpace (points B S hS X) :=
    pointTopology B S hS X
  let e := openSubspacesOrderIso B S hS X hX
  have hle : e ⟨U, hU⟩ ≤ e ⟨V, hV⟩ := by
    change (e ⟨U, hU⟩).1 ⊆ (e ⟨V, hV⟩).1
    simpa only [e, openSubspacesOrderIso_apply] using hpoints
  exact e.le_iff_le.mp hle

private theorem isOpenSubspace_range_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Y : Subfunctor X) (hY : IsOpenSubspace B S hS Y)
    (A : Subfunctor Y.toFunctor) (hA : IsOpenSubspace B S hS A) :
    IsOpenSubspace B S hS
      (Subfunctor.range (A.ι ≫ Y.ι)) := by
  have : Mono (A.ι ≫ Y.ι) := inferInstance
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : P.IsMultiplicative := inferInstance
  let : (yoneda (C := BigFppfOver B S hS)).Full := inferInstance
  let : (yoneda (C := BigFppfOver B S hS)).Faithful := inferInstance
  let : MorphismProperty.IsMultiplicative P.presheaf :=
    MorphismProperty.relative_isMultiplicative P
  exact isOpenSubspace_range_of_open B S hS (A.ι ≫ Y.ι) hA.1
    ((inferInstance : MorphismProperty.IsMultiplicative P.presheaf).comp_mem
      A.ι Y.ι hA.2 hY.2)

private theorem points_cover_of_elementaryDistinguishedSquare
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W)
    (U : Subfunctor W) (f : V ⟶ W)
    (hsq : IsElementaryDistinguishedSquare B S hS hW U f) :
    Set.range (pointsMap B S hS U.toFunctor U.ι) ∪
      Set.range (pointsMap B S hS V f) =
        Set.range (pointsMap B S hS W (𝟙 W)) := by
  classical
  let C := (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ
  let Z := reducedClosedSubspace B S hS W hW C hsq.isClosedComplement
  have hZsupport : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = C :=
    range_pointsMap_ι_reducedClosedSubspace B S hS W hW C hsq.isClosedComplement
  have : IsIso (Z.fromPreimage f) := by simpa [Z, C] using hsq.isIsoOverComplement
  rw [pointsMap_id, Set.range_id]
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  by_cases hyU : x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)
  · exact Or.inl hyU
  obtain ⟨z, rfl⟩ : x ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
    rw [hZsupport]
    exact hyU
  obtain ⟨y, rfl⟩ := pointsMap_surjective_of_iso B S hS (asIso (Z.fromPreimage f)) z
  refine Or.inr ⟨pointsMap B S hS (Z.preimage f).toFunctor (Z.preimage f).ι y, ?_⟩
  simpa only [pointsMap_comp, Function.comp_apply, asIso_hom] using
    congrFun (congrArg (pointsMap B S hS _) (Subfunctor.fromPreimage_ι Z f)).symm y

/-- A point whose image under a monomorphism `k` is the image of a point `a` under `u ≫ k` is
the image of `a` under `u`. -/
private theorem eq_pointsMap_of_pointsMap_comp_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (u : E ⟶ F) (k : F ⟶ G) [Mono k]
    (p : points B S hS F) (a : points B S hS E)
    (h : pointsMap B S hS F k p = pointsMap B S hS E (u ≫ k) a) :
    p = pointsMap B S hS E u a :=
  pointsMap_injective_of_mono B S hS k (h.trans (pointsMap_comp_apply B S hS u k a))

/-- Two maps in opposite directions which are compatible with monomorphisms `i` and `j` out of
their sources are inverse isomorphisms. -/
private theorem isIso_of_comp_eq_of_mono {C : Type*} [Category C] {A B D : C} (a : A ⟶ B)
    (b : B ⟶ A) (i : A ⟶ D) (j : B ⟶ D) [Mono i] [Mono j] (hb : b ≫ i = j) (ha : a ≫ j = i) :
    IsIso a :=
  ⟨⟨b, (cancel_mono i).1 (by rw [Category.assoc, hb, ha, Category.id_comp]),
    (cancel_mono j).1 (by rw [Category.assoc, ha, hb, Category.id_comp])⟩⟩

private theorem isElementaryDistinguishedSquare_openEnlargement
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Subfunctor X)
    (Y : Subfunctor X) (hY : IsOpenSubspace B S hS Y)
    (A : Subfunctor Y.toFunctor)
    (U : Subfunctor X)
    (hUrange : Set.range (pointsMap B S hS U.toFunctor U.ι) =
      Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ Y.ι)))
    (L D : Subfunctor X)
    (hL : IsOpenSubspace B S hS L)
    (hD : IsOpenSubspace B S hS D)
    (hLrange : Set.range (pointsMap B S hS L.toFunctor L.ι) =
      Set.range (pointsMap B S hS W.toFunctor W.ι) ∪
        Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hDrange : Set.range (pointsMap B S hS D.toFunctor D.ι) =
      Set.range (pointsMap B S hS W.toFunctor W.ι) ∪
        Set.range (pointsMap B S hS Y.toFunctor Y.ι))
    (hLD : L ≤ D) (hYD : Y ≤ D)
    (hWY : Set.range (pointsMap B S hS W.toFunctor W.ι) ∩
        Set.range (pointsMap B S hS Y.toFunctor Y.ι) ⊆
      Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ Y.ι)))
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : V ⟶ Y.toFunctor)
    (hsq : IsElementaryDistinguishedSquare B S hS hY.1 A f) :
    IsElementaryDistinguishedSquare B S hS hD.1
      (Subfunctor.range (Subfunctor.homOfLe hLD))
      (f ≫ Subfunctor.homOfLe hYD) := by
  let LD := Subfunctor.homOfLe hLD
  let YD := Subfunctor.homOfLe hYD
  let Left := Subfunctor.range LD
  let RY := Subfunctor.range YD
  have : Mono LD := inferInstance
  have : Mono YD := inferInstance
  have hLeft : IsOpenSubspace B S hS Left :=
    isOpenSubspace_of_le B S hS L D hL hLD
  have hRY : IsOpenSubspace B S hS RY :=
    isOpenSubspace_of_le B S hS Y D hY hYD
  have hAleftRange : Set.range
      (pointsMap B S hS Left.toFunctor Left.ι) =
      Set.range (pointsMap B S hS L.toFunctor LD) :=
    range_pointsMap_range B S hS LD
  have hRYrange : Set.range
      (pointsMap B S hS RY.toFunctor RY.ι) =
      Set.range (pointsMap B S hS Y.toFunctor YD) :=
    range_pointsMap_range B S hS YD
  have hLcomp : LD ≫ D.ι = L.ι := Subfunctor.homOfLe_ι hLD
  have hYcomp : YD ≫ D.ι = Y.ι := Subfunctor.homOfLe_ι hYD
  have hLeftPoint : ∀ p : points B S hS D.toFunctor,
      pointsMap B S hS D.toFunctor D.ι p ∈
        Set.range (pointsMap B S hS L.toFunctor L.ι) →
      p ∈ Set.range (pointsMap B S hS Left.toFunctor Left.ι) := by
    rintro p ⟨l, hl⟩
    rw [hAleftRange]
    exact ⟨l, (eq_pointsMap_of_pointsMap_comp_eq B S hS LD D.ι p l
      (by rw [hLcomp]; exact hl.symm)).symm⟩
  let : TopologicalSpace (points B S hS D.toFunctor) :=
    pointTopology B S hS D.toFunctor
  let eD := openSubspacesOrderIso B S hS D.toFunctor hD.1
  have hclosed : @IsClosed _ (pointTopology B S hS D.toFunctor)
      (Set.range (pointsMap B S hS Left.toFunctor Left.ι))ᶜ := by
    apply isClosed_compl_iff.mpr
    rw [← openSubspacesOrderIso_apply
      B S hS D.toFunctor hD.1 ⟨Left, hLeft⟩]
    exact (eD ⟨Left, hLeft⟩).2
  let CD := reducedClosedSubspace B S hS D.toFunctor hD.1
    (Set.range (pointsMap B S hS Left.toFunctor Left.ι))ᶜ hclosed
  have hCDclosed : IsClosedSubspace B S hS CD :=
    isClosedSubspace_reducedClosedSubspace B S hS D.toFunctor hD.1 _ hclosed
  have hCDred : HasEtaleLocalProperty B S hS CD.toFunctor
      (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS D.toFunctor hD.1 _ hclosed
  have hCZrange : Set.range (pointsMap B S hS CD.toFunctor CD.ι) =
      (Set.range (pointsMap B S hS Left.toFunctor Left.ι))ᶜ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS D.toFunctor hD.1 _ hclosed
  have hCnotLeft : ∀ c, pointsMap B S hS CD.toFunctor CD.ι c ∉
      Set.range (pointsMap B S hS Left.toFunctor Left.ι) := fun c h => by
    have hc : pointsMap B S hS CD.toFunctor CD.ι c ∈
        Set.range (pointsMap B S hS CD.toFunctor CD.ι) := ⟨c, rfl⟩
    rw [hCZrange] at hc
    exact hc h
  let CY := reducedClosedSubspace B S hS Y.toFunctor hY.1
    (Set.range (pointsMap B S hS A.toFunctor A.ι))ᶜ
    hsq.isClosedComplement
  have hCYclosed : IsClosedSubspace B S hS CY :=
    isClosedSubspace_reducedClosedSubspace B S hS Y.toFunctor hY.1 _
      hsq.isClosedComplement
  have hCYred : HasEtaleLocalProperty B S hS CY.toFunctor
      (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS Y.toFunctor hY.1 _
      hsq.isClosedComplement
  have hCYrange : Set.range (pointsMap B S hS CY.toFunctor CY.ι) =
      (Set.range (pointsMap B S hS A.toFunctor A.ι))ᶜ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS Y.toFunctor hY.1 _
      hsq.isClosedComplement
  have hCZimage : Set.range (pointsMap B S hS CD.toFunctor CD.ι) ⊆
      Set.range (pointsMap B S hS RY.toFunctor RY.ι) := by
    intro p hp
    rcases hp with ⟨c, rfl⟩
    let x := pointsMap B S hS D.toFunctor D.ι
      (pointsMap B S hS CD.toFunctor CD.ι c)
    have hxZ : x ∈ Set.range (pointsMap B S hS D.toFunctor D.ι) :=
      ⟨pointsMap B S hS CD.toFunctor CD.ι c, rfl⟩
    rw [hDrange] at hxZ
    rcases hxZ with hxW | hxY
    · refine (hCnotLeft c (hLeftPoint _ ?_)).elim
      rw [hLrange]
      exact Or.inl hxW
    · obtain ⟨y, hy⟩ := hxY
      have hpEq := eq_pointsMap_of_pointsMap_comp_eq B S hS YD D.ι
        (pointsMap B S hS CD.toFunctor CD.ι c) y (by rw [hYcomp]; exact hy.symm)
      rw [hpEq, hRYrange]
      exact ⟨y, rfl⟩
  obtain ⟨g₀, hg₀⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS
      hD.1 hCDclosed.1 RY hRY CD.ι).2 hCZimage
  let tY := Subfunctor.toRange YD
  have : IsIso tY := inferInstance
  let g := g₀ ≫ inv tY
  have hg : g ≫ YD = CD.ι := by
    have ht : tY ≫ RY.ι = YD := Subfunctor.toRange_ι YD
    dsimp [g]
    calc
      g₀ ≫ inv tY ≫ YD = g₀ ≫ inv tY ≫ (tY ≫ RY.ι) := by rw [ht]
      _ = g₀ ≫ RY.ι := by simp
      _ = CD.ι := hg₀
  have hCZtoCY : Set.range (pointsMap B S hS CD.toFunctor g) ⊆
      Set.range (pointsMap B S hS CY.toFunctor CY.ι) := by
    rintro _ ⟨c, rfl⟩
    rw [hCYrange]
    rintro ⟨a, ha⟩
    refine hCnotLeft c (hLeftPoint _ ?_)
    rw [hLrange, hUrange]
    refine Or.inr ⟨a, ?_⟩
    rw [pointsMap_comp_apply B S hS A.ι Y.ι, ha, ← pointsMap_comp_apply B S hS g Y.ι,
      ← pointsMap_comp_apply B S hS CD.ι D.ι, ← hg, Category.assoc g YD D.ι, hYcomp]
  obtain ⟨aMap, haMap⟩ :=
    (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS
      Y.toFunctor hY.1 _ hsq.isClosedComplement hCDclosed.1 hCDred g).2
      (by rw [← hCYrange]; exact hCZtoCY)
  have hCYtoCZ : Set.range (pointsMap B S hS CY.toFunctor
      (CY.ι ≫ YD)) ⊆
      Set.range (pointsMap B S hS CD.toFunctor CD.ι) := by
    rintro _ ⟨c, rfl⟩
    rw [hCZrange]
    intro hleft
    rw [hAleftRange] at hleft
    obtain ⟨l, hl⟩ := hleft
    have hxL : pointsMap B S hS CY.toFunctor (CY.ι ≫ Y.ι) c ∈
        Set.range (pointsMap B S hS L.toFunctor L.ι) := by
      refine ⟨l, ?_⟩
      rw [← hLcomp, pointsMap_comp_apply B S hS LD D.ι l, hl,
        ← pointsMap_comp_apply B S hS (CY.ι ≫ YD) D.ι, Category.assoc, hYcomp]
    rw [hLrange, hUrange] at hxL
    have hxA : pointsMap B S hS CY.toFunctor (CY.ι ≫ Y.ι) c ∈
        Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ Y.ι)) := by
      rcases hxL with hW | hA
      · exact hWY ⟨hW, ⟨_, (pointsMap_comp_apply B S hS CY.ι Y.ι c).symm⟩⟩
      · exact hA
    obtain ⟨a, ha⟩ := hxA
    have hca := eq_pointsMap_of_pointsMap_comp_eq B S hS A.ι Y.ι
      (pointsMap B S hS CY.toFunctor CY.ι c) a
      ((pointsMap_comp_apply B S hS CY.ι Y.ι c).symm.trans ha.symm)
    have hc : pointsMap B S hS CY.toFunctor CY.ι c ∈
        Set.range (pointsMap B S hS CY.toFunctor CY.ι) := ⟨c, rfl⟩
    rw [hCYrange] at hc
    exact hc ⟨a, hca.symm⟩
  obtain ⟨bMap, hbMap⟩ :=
    (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS
      D.toFunctor hD.1 _ hclosed hCYclosed.1 hCYred (CY.ι ≫ YD)).2
      (by rw [← hCZrange]; exact hCYtoCZ)
  have : IsIso aMap := isIso_of_comp_eq_of_mono aMap bMap CD.ι (CY.ι ≫ YD) hbMap
    (by rw [← Category.assoc, haMap, hg])
  let CYpre := CY.preimage f
  let CDpre := CD.preimage (f ≫ YD)
  let CYmap := CY.fromPreimage f
  let CDmap := CD.fromPreimage (f ≫ YD)
  have hCYpull := CategoryTheory.Subfunctor.isPullback_preimage f CY
  have hCZpull := CategoryTheory.Subfunctor.isPullback_preimage (f ≫ YD) CD
  have heq : (CDmap ≫ aMap) ≫ CY.ι = CDpre.ι ≫ f := by
    apply (cancel_mono YD).1
    calc
      (CDmap ≫ aMap ≫ CY.ι) ≫ YD =
          CDmap ≫ (aMap ≫ CY.ι) ≫ YD := by simp [Category.assoc]
      _ = CDmap ≫ (g ≫ YD) := by rw [haMap]
      _ = CDmap ≫ CD.ι := by rw [hg]
      _ = CDpre.ι ≫ (f ≫ YD) := Subfunctor.fromPreimage_ι CD (f ≫ YD)
      _ = (CDpre.ι ≫ f) ≫ YD := by simp [Category.assoc]
  let epre := hCYpull.lift (CDmap ≫ aMap) CDpre.ι heq
  have hepreMap : epre ≫ CYmap = CDmap ≫ aMap :=
    hCYpull.lift_fst (CDmap ≫ aMap) CDpre.ι heq
  have hepreIn : epre ≫ CYpre.ι = CDpre.ι :=
    hCYpull.lift_snd (CDmap ≫ aMap) CDpre.ι heq
  have hdeq : (CYmap ≫ bMap) ≫ CD.ι = CYpre.ι ≫ (f ≫ YD) := by
    calc
      (CYmap ≫ bMap) ≫ CD.ι = CYmap ≫ (bMap ≫ CD.ι) := by rw [Category.assoc]
      _ = CYmap ≫ (CY.ι ≫ YD) := by rw [hbMap]
      _ = (CYpre.ι ≫ f) ≫ YD := by
            change (CY.fromPreimage f ≫ CY.ι) ≫ YD = _
            rw [Subfunctor.fromPreimage_ι]
      _ = CYpre.ι ≫ (f ≫ YD) := by simp [Category.assoc]
  let dpre := hCZpull.lift (CYmap ≫ bMap) CYpre.ι hdeq
  have hdpreIn : dpre ≫ CDpre.ι = CYpre.ι :=
    hCZpull.lift_snd (CYmap ≫ bMap) CYpre.ι hdeq
  have : IsIso epre := isIso_of_comp_eq_of_mono epre dpre CDpre.ι CYpre.ι hdpreIn hepreIn
  have : IsIso CYmap := hsq.isIsoOverComplement
  have hmapEq : CDmap = epre ≫ CYmap ≫ inv aMap := by
    apply (cancel_mono aMap).1
    calc
      CDmap ≫ aMap = epre ≫ CYmap := hepreMap.symm
      _ = (epre ≫ CYmap ≫ inv aMap) ≫ aMap := by simp [Category.assoc]
  have hCDmapIso : IsIso CDmap := by
    rw [hmapEq]
    infer_instance
  have hYZet : IsEtale B S hS YD :=
    isEtale_of_isOpenSubspace_range B S hS YD hRY
  have hFZet : IsEtale B S hS (f ≫ YD) :=
    isEtale_comp B S hS hsq.isEtale hYZet
  exact ⟨hsq.isAlgebraicSpace, hLeft, hFZet, hclosed, hCDmapIso⟩


/-- An elementary distinguished square inside an algebraic space `Wp` which sits as an open
subspace `Y` of `X`, transported to the ambient `Y` and with its open member enlarged by the
part of `W` lying in `Y`. -/
theorem exists_transported_square
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Wp V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hWpalg : IsAlgebraicSpace B S hS Wp)
    (W : Subfunctor X) (hWopen : IsOpenSubspace B S hS W)
    (Y : Subfunctor X) (hYopen : IsOpenSubspace B S hS Y)
    (gW : Wp ⟶ X) (eY : Wp ≅ Y.toFunctor) (hEY : eY.hom ≫ Y.ι = gW)
    (U : Subfunctor Wp) (f : V ⟶ Wp)
    (hsqf : IsElementaryDistinguishedSquare B S hS hWpalg U f)
    (hVaff : IsAffineSpace B S hS V) :
    ∃ (A : Subfunctor Y.toFunctor) (V₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (f₄ : V₄ ⟶ Y.toFunctor),
      IsElementaryDistinguishedSquare B S hS hYopen.1 A f₄ ∧
      IsAffineSpace B S hS V₄ ∧
      Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ Y.ι)) =
        Set.range (pointsMap B S hS U.toFunctor (U.ι ≫ gW)) ∪
          (Set.range (pointsMap B S hS W.toFunctor W.ι) ∩
            Set.range (pointsMap B S hS Wp gW)) := by
  classical
  obtain ⟨Up, hUpopen, hUppts⟩ :=
    exists_openSubspace_of_isOpen B S hS hWpalg
      (Set.range (pointsMap B S hS U.toFunctor U.ι) ∪
        pointsMap B S hS Wp gW ⁻¹' Set.range (pointsMap B S hS W.toFunctor W.ι))
      ((isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι
        hsqf.isOpenSubspace.2).union
          ((isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hWopen.2).preimage
            (continuous_pointsMap B S hS gW)))
  have hUUp : U ≤ Up :=
    open_le_of_points B S hS Wp hWpalg U Up hsqf.isOpenSubspace hUpopen
      (by rw [hUppts]; exact Set.subset_union_left)
  obtain ⟨W₃, hW₃open, hUpW₃, f₃, hW₃range, _hcomm₃, hsq₃⟩ :=
    isElementaryDistinguishedSquare_openRestriction B S hS hWpalg U f hsqf
      (⊤ : Subfunctor V) (AlgebraicGeometry.Space.isOpenSubspace_top hsqf.isAlgebraicSpace)
      Up hUpopen hUUp
  have htopWp : Set.range (pointsMap B S hS (⊤ : Subfunctor Wp).toFunctor
      (⊤ : Subfunctor Wp).ι) = Set.univ :=
    (pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor Wp).ι).range_eq
  have htopVsurj : Set.range (pointsMap B S hS (⊤ : Subfunctor V).toFunctor
      (⊤ : Subfunctor V).ι) = Set.univ :=
    (pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor V).ι).range_eq
  have htopV : Set.range (pointsMap B S hS (⊤ : Subfunctor V).toFunctor
      ((⊤ : Subfunctor V).ι ≫ f)) = Set.range (pointsMap B S hS V f) := by
    rw [pointsMap_comp, Set.range_comp, htopVsurj, Set.image_univ]
  have hW₃top : W₃ = ⊤ := by
    refine openSubspace_eq_of_pointsMap_range_eq B S hS hWpalg W₃ ⊤ hW₃open
      (AlgebraicGeometry.Space.isOpenSubspace_top hWpalg) ?_
    have hcov := points_cover_of_elementaryDistinguishedSquare B S hS hWpalg U f hsqf
    rw [pointsMap_id, Set.range_id] at hcov
    rw [hW₃range, htopWp, hUppts, htopV]
    refine Set.eq_univ_of_subset ?_ hcov
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  subst hW₃top
  set e₂ : Y.toFunctor ≅ (⊤ : Subfunctor Wp).toFunctor :=
    eY.symm ≪≫ (asIso (⊤ : Subfunctor Wp).ι).symm with he₂
  have hpcomp : e₂.hom ≫ ((⊤ : Subfunctor Wp).ι ≫ gW) = Y.ι := by
    rw [he₂]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv]
    rw [Category.assoc, ← Category.assoc (inv (⊤ : Subfunctor Wp).ι),
      IsIso.inv_hom_id, Category.id_comp, ← hEY, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  refine ⟨(Subfunctor.range (Subfunctor.homOfLe hUpW₃)).preimage e₂.hom,
    pullback f₃ e₂.hom, pullback.snd f₃ e₂.hom,
    isElementaryDistinguishedSquare_preimage B S hS hW₃open.1 hYopen.1
      (Subfunctor.range (Subfunctor.homOfLe hUpW₃)) f₃ hsq₃ e₂.hom, ?_, ?_⟩
  · have hfstIso : IsIso (pullback.fst f₃ e₂.hom) :=
      (IsPullback.of_hasPullback f₃ e₂.hom).isIso_fst_of_isIso
    exact IsAffineSpace.of_iso hVaff
      ((asIso (⊤ : Subfunctor V).ι).symm ≪≫ (asIso (pullback.fst f₃ e₂.hom)).symm)
  · rw [← hpcomp, range_pointsMap_preimage_isoHom B S hS e₂
        (Subfunctor.range (Subfunctor.homOfLe hUpW₃)) ((⊤ : Subfunctor Wp).ι ≫ gW),
      range_pointsMap_range_comp B S hS (Subfunctor.homOfLe hUpW₃)
        ((⊤ : Subfunctor Wp).ι ≫ gW),
      ← Category.assoc, Subfunctor.homOfLe_ι, pointsMap_comp, Set.range_comp, hUppts,
      Set.image_union, Set.image_preimage_eq_inter_range, ← Set.range_comp,
      ← pointsMap_comp]

/-- The inductive step for Stacks 09IT: the property passes from the open subspaces
containing `W` across an elementary distinguished square whose ambient space is an open
subspace `Y` of `X`, after adjoining `W`. -/
theorem enlargement_step
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Wp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (W : Subfunctor X) (hWopen : IsOpenSubspace B S hS W)
    (hWqc : IsQuasiCompactSpace B S hS W.toFunctor)
    (P : Subfunctor X → Prop)
    (hstep : ∀ (W₁ W₂ : Subfunctor X) (_hW₁ : IsOpenSubspace B S hS W₁)
      (hW₂ : IsOpenSubspace B S hS W₂),
      IsQuasiCompactSpace B S hS W₁.toFunctor →
      IsQuasiCompactSpace B S hS W₂.toFunctor →
      ∀ hle : W₁ ≤ W₂, W ≤ W₁ →
      ∀ {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W₂.toFunctor),
        IsAffineSpace B S hS V →
        IsElementaryDistinguishedSquare B S hS hW₂.1
          (Subfunctor.range (Subfunctor.homOfLe hle)) f →
        P W₁ → P W₂)
    (Y : Subfunctor X) (hYopen : IsOpenSubspace B S hS Y)
    (gW : Wp ⟶ X)
    (hYpts : Set.range (pointsMap B S hS Y.toFunctor Y.ι) =
      Set.range (pointsMap B S hS Wp gW))
    (U : Subfunctor Wp) (hUopen : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hQU : ∀ D : Subfunctor X, IsOpenSubspace B S hS D →
      IsQuasiCompactSpace B S hS D.toFunctor → W ≤ D →
      Set.range (pointsMap B S hS D.toFunctor D.ι) =
        Set.range (pointsMap B S hS W.toFunctor W.ι) ∪
          Set.range (pointsMap B S hS U.toFunctor (U.ι ≫ gW)) → P D)
    (A : Subfunctor Y.toFunctor) {V₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f₄ : V₄ ⟶ Y.toFunctor)
    (hsq₄ : IsElementaryDistinguishedSquare B S hS hYopen.1 A f₄)
    (hV₄aff : IsAffineSpace B S hS V₄)
    (hApts : Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ Y.ι)) =
      Set.range (pointsMap B S hS U.toFunctor (U.ι ≫ gW)) ∪
        (Set.range (pointsMap B S hS W.toFunctor W.ι) ∩
          Set.range (pointsMap B S hS Wp gW)))
    (D : Subfunctor X) (hDopen : IsOpenSubspace B S hS D)
    (hDqc : IsQuasiCompactSpace B S hS D.toFunctor)
    (hDrange : Set.range (pointsMap B S hS D.toFunctor D.ι) =
      Set.range (pointsMap B S hS W.toFunctor W.ι) ∪
        Set.range (pointsMap B S hS Wp gW)) :
    P D := by
  classical
  let : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  have hWptsOpen : IsOpen (Set.range (pointsMap B S hS W.toFunctor W.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hWopen.2
  have hA'open : IsOpenSubspace B S hS (Subfunctor.range (A.ι ≫ Y.ι)) :=
    isOpenSubspace_range_comp B S hS Y hYopen A hsq₄.isOpenSubspace
  have hA'pts : Set.range (pointsMap B S hS (Subfunctor.range (A.ι ≫ Y.ι)).toFunctor
      (Subfunctor.range (A.ι ≫ Y.ι)).ι) =
      Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ Y.ι)) :=
    range_pointsMap_range B S hS (A.ι ≫ Y.ι)
  have hAptsOpen : IsOpen (Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ Y.ι))) := by
    rw [← hA'pts]
    exact isOpen_range_pointsMap_of_isOpenImmersion B S hS
      (Subfunctor.range (A.ι ≫ Y.ι)).ι hA'open.2
  obtain ⟨L, hLopen, hLpts⟩ := exists_openSubspace_of_isOpen B S hS hX
    (Set.range (pointsMap B S hS W.toFunctor W.ι) ∪
      Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ Y.ι)))
    (hWptsOpen.union hAptsOpen)
  have hUXsub : Set.range (pointsMap B S hS U.toFunctor (U.ι ≫ gW)) ⊆
      Set.range (pointsMap B S hS Wp gW) := by
    rw [pointsMap_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  have hWL : W ≤ L := open_le_of_points B S hS X hX W L hWopen hLopen
    (by rw [hLpts]; exact Set.subset_union_left)
  have hLpts' : Set.range (pointsMap B S hS L.toFunctor L.ι) =
      Set.range (pointsMap B S hS W.toFunctor W.ι) ∪
        Set.range (pointsMap B S hS U.toFunctor (U.ι ≫ gW)) := by
    rw [hLpts, hApts]
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff]
    tauto
  have hLqc : IsQuasiCompactSpace B S hS L.toFunctor := by
    refine openSubspace_isQuasiCompact_of_compact_range B S hS hX L hLopen ?_
    rw [hLpts']
    exact (pointsRange_isCompact B S hS hWopen.1 hX W.ι hWqc).union
      (pointsRange_isCompact B S hS hUopen.1 hX (U.ι ≫ gW) hUqc)
  have hPL : P L := hQU L hLopen hLqc hWL hLpts'
  have hLD : L ≤ D := by
    refine open_le_of_points B S hS X hX L D hLopen hDopen ?_
    rw [hLpts, hApts, hDrange]
    rintro x (hx | hx | hx)
    exacts [Or.inl hx, Or.inr (hUXsub hx), Or.inl hx.1]
  have hYD : Y ≤ D := by
    refine open_le_of_points B S hS X hX Y D hYopen hDopen ?_
    rw [hYpts, hDrange]
    exact Set.subset_union_right
  refine hstep L D hLopen hDopen hLqc hDqc hLD hWL
    (f₄ ≫ Subfunctor.homOfLe hYD) hV₄aff ?_ hPL
  refine isElementaryDistinguishedSquare_openEnlargement B S hS W Y hYopen A
    (Subfunctor.range (A.ι ≫ Y.ι)) hA'pts L D hLopen hDopen ?_ ?_ hLD hYD ?_ f₄ hsq₄
  · rw [hLpts, hA'pts]
  · rw [hDrange, hYpts]
  · rw [hApts, hYpts]
    exact Set.subset_union_right

end AlgebraicGeometry.Space

end
