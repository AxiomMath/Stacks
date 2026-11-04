module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreservingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluing
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsNestedRestriction

/-!
# Extending morphisms from locally Noetherian schemes on a big fppf site

Let `S` be a locally Noetherian scheme contained in a big fppf site `B`, and let `F` and `G` be
fppf sheaves on the big fppf site `BigFppfOver B S hS` of `S` which are limit preserving in the
sense of Stacks 049J. Every transformation between the restrictions of `F` and `G` to the locally
Noetherian objects of the site is the restriction of exactly one transformation `F ⟶ G`.

This is the full faithfulness half of **Stacks 0GE3** for the big fppf site of `S`. The library
proves Stacks 0GE3 for functors on the slice `Sch/S` of *all* schemes
(`AlgebraicGeometry.ExtendingFunctors.isEquivalence_limitPreservingRestriction_noetherian`); the
algebraic spaces of this library are functors on the size-bounded site `BigFppfOver B S hS`, to
which that statement does not apply. Here the site is identified with the full subcategory of
`Sch/S` on the objects contained in `B`, which satisfies conditions (1) and (2) of Stacks 0EUW, and
the statement is deduced from the version of Stacks 0GE3 for two nested full subcategories,
`AlgebraicGeometry.ExtendingFunctors.existsUnique_hom_whiskerLeft_ιOfLE_eq`.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.IsContainedOver`: the objects of `Sch/S` whose underlying
  scheme is contained in the big fppf site `B`.
* `AlgebraicGeometry.ExtendingFunctors.bigFppfOverEquivalence`: the big fppf site of `S` is
  equivalent to that full subcategory of `Sch/S`.
* `AlgebraicGeometry.ExtendingFunctors.locallyNoetherianOverEquivalence`: likewise for the locally
  Noetherian objects.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.isZariskiSheafOnSubcategory_of_isSheaf` and
  `AlgebraicGeometry.ExtendingFunctors.preservesAffineLimitsOnSubcategory_of_limitPreserving`: an
  fppf sheaf on the site satisfies condition (a) of Stacks 0EUW, and a limit preserving functor on
  the site in the sense of Stacks 049J satisfies condition (b).
* `AlgebraicGeometry.ExtendingFunctors.existsUnique_hom_whiskerLeft_eq_bigFppfOver`: **Stacks
  0GE3** for the big fppf site of `S`, full faithfulness of the restriction to locally Noetherian
  objects.
* `AlgebraicGeometry.ExtendingFunctors.existsUnique_iso_isoWhiskerLeft_eq_bigFppfOver`: the same
  for isomorphisms.

## Implementation notes

The essential surjectivity half of Stacks 0GE3, that every limit preserving sheaf on the locally
Noetherian objects of the site is a restriction, is not proved here, so no declaration of this
file carries the tag. The full faithfulness proved here is what the proof of Stacks 0GHC uses: it
constructs a morphism of algebraic spaces from a transformation of their functors of points on
locally Noetherian schemes.

The values of `F` and `G` are lifted to `Type (max w (u + 1))`, the universe in which the
extension of Stacks 0EUW takes its values; `uliftFunctor` is fully faithful and preserves
colimits, so nothing is lost.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-! ### The big fppf site as a full subcategory of `Sch/S` -/

/-- The objects of `Sch/S` whose underlying scheme is contained in the big fppf site `B`, that
is satisfies its size cutoff. -/
def IsContainedOver : ObjectProperty (Over S) := fun Y => B.Contains Y.left

/-- The objects of `Sch/S` whose underlying scheme is contained in the big fppf site `B` and is
locally Noetherian. -/
def IsContainedLocallyNoetherianOver : ObjectProperty (Over S) :=
  fun Y => B.Contains Y.left ∧ IsLocallyNoetherian Y.left

/-- Every locally Noetherian object of `Sch/S` contained in `B` is an object contained in `B`. -/
lemma isContainedLocallyNoetherianOver_le :
    IsContainedLocallyNoetherianOver B (S := S) ≤ IsContainedOver B := fun _ h => h.1

/-- An object of `Sch/S` contained in `B`, regarded as an object of the big fppf site of `S`. -/
@[simps]
def toBigFppfOver : (IsContainedOver B (S := S)).FullSubcategory ⥤ BigFppfOver B S hS where
  obj Y := siteObject B S hS Y.property Y.obj.hom
  map {Y Y'} f := Over.homMk (ObjectProperty.homMk f.hom.left)
    (ObjectProperty.hom_ext _ (Over.w f.hom))

/-- An object of the big fppf site of `S`, regarded as an object of `Sch/S` contained in `B`. -/
@[simps]
def fromBigFppfOver : BigFppfOver B S hS ⥤ (IsContainedOver B (S := S)).FullSubcategory where
  obj X := ⟨Over.mk X.hom.hom, X.left.property⟩
  map {X X'} f := ObjectProperty.homMk (Over.homMk f.left.hom
    (congrArg (fun g => g.hom) (Over.w f)))

/-- **The big fppf site of `S` is the full subcategory of `Sch/S` on the objects contained in
`B`.** The two functors are mutually inverse on the nose. -/
def bigFppfOverEquivalence :
    BigFppfOver B S hS ≌ (IsContainedOver B (S := S)).FullSubcategory where
  functor := fromBigFppfOver B hS
  inverse := toBigFppfOver B hS
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- A locally Noetherian object of `Sch/S` contained in `B`, regarded as a locally Noetherian
object of the big fppf site of `S`. -/
@[simps]
def toLocallyNoetherianOver :
    (IsContainedLocallyNoetherianOver B (S := S)).FullSubcategory ⥤ LocallyNoetherianOver B S hS
    where
  obj Y := ⟨siteObject B S hS Y.property.1 Y.obj.hom, Y.property.2⟩
  map {Y Y'} f := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk f.hom.left)
    (ObjectProperty.hom_ext _ (Over.w f.hom)))

/-- A locally Noetherian object of the big fppf site of `S`, regarded as a locally Noetherian
object of `Sch/S` contained in `B`. -/
@[simps]
def fromLocallyNoetherianOver :
    LocallyNoetherianOver B S hS ⥤ (IsContainedLocallyNoetherianOver B (S := S)).FullSubcategory
    where
  obj X := ⟨Over.mk X.obj.hom.hom, X.obj.left.property, X.property⟩
  map {X X'} f := ObjectProperty.homMk (Over.homMk f.hom.left.hom
    (congrArg (fun g => g.hom) (Over.w f.hom)))

/-- The locally Noetherian objects of the big fppf site of `S` are the full subcategory of
`Sch/S` on the locally Noetherian objects contained in `B`. -/
def locallyNoetherianOverEquivalence :
    LocallyNoetherianOver B S hS ≌ (IsContainedLocallyNoetherianOver B (S := S)).FullSubcategory
    where
  functor := fromLocallyNoetherianOver B hS
  inverse := toLocallyNoetherianOver B hS
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-! ### Conditions (1) and (2) of Stacks 0EUW -/

include hS in
/-- An affine scheme of finite presentation over an affine open of a scheme contained in `B` is
contained in `B`. -/
theorem contains_of_finitePresentation {U : S.affineOpens} {V : Scheme.{u}}
    (g : V ⟶ U.1.toScheme) [IsAffine V] (hg : FinitePresentation g) : B.Contains V := by
  have hU : IsAffine U.1.toScheme := U.2
  have : LocallyOfFinitePresentation g := hg.1
  have hft : LocallyOfFiniteType g := inferInstance
  have hrft : (g.appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hft
  let : Algebra Γ(U.1.toScheme, ⊤) Γ(V, ⊤) := (g.appTop).hom.toAlgebra
  have : Algebra.FiniteType Γ(U.1.toScheme, ⊤) Γ(V, ⊤) := hrft
  have hR : (Spec (CommRingCat.of Γ(U.1.toScheme, ⊤))).size < B.cutoff :=
    calc (Spec (CommRingCat.of Γ(U.1.toScheme, ⊤))).size = U.1.toScheme.size :=
          Scheme.size_congr U.1.toScheme.isoSpec.symm
      _ ≤ S.size := Scheme.size_coe_opens_le S U.1
      _ < B.cutoff := hS
  have hV := Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    Γ(U.1.toScheme, ⊤) Γ(V, ⊤) hR
  exact (Scheme.size_congr V.isoSpec).trans_lt hV

/-- **Condition (1) of Stacks 0EUW for the objects contained in `B`.** -/
theorem hasAffineOpens_isContainedOver : HasAffineOpens (IsContainedOver B (S := S)) :=
  fun X hX V => ⟨overOpen X V.1, (Scheme.size_coe_opens_le X.left V.1).trans_lt hX,
    ⟨Iso.refl _⟩⟩

include hS in
/-- **Condition (2) of Stacks 0EUW for the objects contained in `B`.** -/
theorem hasFinitePresentationAffines_isContainedOver :
    HasFinitePresentationAffines (IsContainedOver B (S := S)) :=
  fun U V g hV hg => ⟨Over.mk (g ≫ U.1.ι),
    have : IsAffine V := hV
    contains_of_finitePresentation B hS (V := V) g hg, ⟨Iso.refl _⟩⟩

/-- **Condition (1) of Stacks 0EUW for the locally Noetherian objects contained in `B`.** -/
theorem hasAffineOpens_isContainedLocallyNoetherianOver :
    HasAffineOpens (IsContainedLocallyNoetherianOver B (S := S)) :=
  fun X hX V =>
    have : IsLocallyNoetherian X.left := hX.2
    ⟨overOpen X V.1, ⟨(Scheme.size_coe_opens_le X.left V.1).trans_lt hX.1,
      isLocallyNoetherian_of_isOpenImmersion V.1.ι⟩, ⟨Iso.refl _⟩⟩

include hS in
/-- **Condition (2) of Stacks 0EUW for the locally Noetherian objects contained in `B`**, over a
locally Noetherian base. -/
theorem hasFinitePresentationAffines_isContainedLocallyNoetherianOver [IsLocallyNoetherian S] :
    HasFinitePresentationAffines (IsContainedLocallyNoetherianOver B (S := S)) :=
  fun U V g hV hg =>
    have : IsAffine V := hV
    have : IsLocallyNoetherian U.1.toScheme := isLocallyNoetherian_of_isOpenImmersion U.1.ι
    have : LocallyOfFinitePresentation g := hg.1
    ⟨Over.mk (g ≫ U.1.ι), ⟨contains_of_finitePresentation B hS (V := V) g hg,
      LocallyOfFiniteType.isLocallyNoetherian (g ≫ U.1.ι)⟩, ⟨Iso.refl _⟩⟩

/-! ### Conditions (a) and (b) of Stacks 0EUW -/

/-- **An fppf sheaf on the big fppf site of `S` is a Zariski sheaf on the objects of `Sch/S`
contained in `B`**, in the sense of the sheaf condition for Zariski coverings by such objects. -/
theorem isCoveringSheafOnSubcategory_of_isSheaf {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    IsCoveringSheafOnSubcategory.{w, u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F) := by
  intro ι X Y f hcov
  rw [ofArrows_mem_coveringPrecoverage_iff] at hcov
  obtain ⟨hsurj, hopen⟩ := hcov
  have hmem := BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS
    (fun i => (toBigFppfOver B hS).obj (Y i)) ((toBigFppfOver B hS).obj X)
    (fun i => (toBigFppfOver B hS).map (f i)) hopen hsurj
  have hsh : (Presieve.ofArrows (fun i => (toBigFppfOver B hS).obj (Y i))
      (fun i => (toBigFppfOver B hS).map (f i))).IsSheafFor F :=
    (Presieve.isSheafFor_iff_generate _).2
      ((isSheaf_iff_isSheaf_of_type _ F).1 hF _ hmem)
  refine isSheafFor_ofArrows_of_existsUnique Y f fun y hy => ?_
  refine existsUnique_section_of_isSheafFor_ofArrows _ _ hsh y fun j j' A a b hab => ?_
  exact hy j j' ((fromBigFppfOver B hS).obj A) ((fromBigFppfOver B hS).map a)
    ((fromBigFppfOver B hS).map b) (by
      have h2 := congrArg (fromBigFppfOver B hS).map hab
      rw [Functor.map_comp, Functor.map_comp] at h2
      exact h2)

/-- **Condition (a) of Stacks 0EUW for an fppf sheaf on the big fppf site of `S`.** -/
theorem isZariskiSheafOnSubcategory_of_isSheaf {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    IsZariskiSheafOnSubcategory (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F ⋙ uliftFunctor.{u + 1}) :=
  isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory .zariski
    (hasAffineOpens_isContainedOver B) (isCoveringSheafOnSubcategory_of_isSheaf B hS
      ((isSheaf_iff_isSheaf_of_type _ _).2
        (Presieve.isSheaf_comp_uliftFunctor _ ((isSheaf_iff_isSheaf_of_type _ F).1 hF))))

/-- **Condition (b) of Stacks 0EUW for a limit preserving functor on the big fppf site of `S`.**
A directed inverse limit in `Sch/S` of affine objects contained in `B` is computed in schemes,
where it is a cofiltered limit of affine schemes with affine limit, to which Stacks 049J
applies. -/
theorem preservesAffineLimitsOnSubcategory_of_limitPreserving
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : LimitPreserving.{u, w, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F) :
    PreservesAffineLimitsOnSubcategory (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F ⋙ uliftFunctor.{u + 1}) := by
  intro Λ _ _ _ D haff c hc
  have hlim : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((toBigFppfOver B hS).mapCone c)) :=
    isLimitOfPreserves (Over.forget S) hc
  have : ∀ i : Λᵒᵖ, IsAffine (((D ⋙ (IsContainedOver B).ι) ⋙ Over.forget S).obj i) := haff
  have hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj ((toBigFppfOver B hS).mapCone c).pt) :=
    Scheme.isAffine_of_isLimit _ (isLimitOfPreserves (Over.forget S) hc)
  obtain ⟨hcol⟩ := hF Λᵒᵖ (D ⋙ toBigFppfOver B hS) ((toBigFppfOver B hS).mapCone c) hlim
    haff hpt
  exact ⟨isColimitOfPreserves uliftFunctor.{u + 1} hcol⟩

/-! ### Stacks 0GE3 for the big fppf site: full faithfulness -/

/-- The functor carrying a functor on the big fppf site of `S` to the corresponding functor on
the objects of `Sch/S` contained in `B`, with values lifted to `Type (max w (u + 1))`. It is fully
faithful. -/
abbrev liftToContainedOver :
    ((BigFppfOver B S hS)ᵒᵖ ⥤ Type w) ⥤
      ((IsContainedOver B (S := S)).FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) :=
  (Functor.whiskeringLeft _ _ _).obj (toBigFppfOver B hS).op ⋙
    (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1}

/-- `AlgebraicGeometry.ExtendingFunctors.liftToContainedOver` is fully faithful. -/
def fullyFaithfulLiftToContainedOver : (liftToContainedOver.{w} B hS).FullyFaithful :=
  ((bigFppfOverEquivalence B hS).op.congrLeft (E := Type w)).fullyFaithfulFunctor.comp
    (fullyFaithfulULiftFunctor.whiskeringRight _)

/-- The analogue of `AlgebraicGeometry.ExtendingFunctors.liftToContainedOver` for the locally
Noetherian objects. -/
abbrev liftToContainedLocallyNoetherianOver :
    ((LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w) ⥤
      ((IsContainedLocallyNoetherianOver B (S := S)).FullSubcategoryᵒᵖ ⥤
        Type (max w (u + 1))) :=
  (Functor.whiskeringLeft _ _ _).obj (toLocallyNoetherianOver B hS).op ⋙
    (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1}

/-- `AlgebraicGeometry.ExtendingFunctors.liftToContainedLocallyNoetherianOver` is fully
faithful. -/
def fullyFaithfulLiftToContainedLocallyNoetherianOver :
    (liftToContainedLocallyNoetherianOver.{w} B hS).FullyFaithful :=
  ((locallyNoetherianOverEquivalence B hS).op.congrLeft (E := Type w)).fullyFaithfulFunctor.comp
    (fullyFaithfulULiftFunctor.whiskeringRight _)

/-- **Stacks 0GE3, full faithfulness, for the big fppf site of `S`.** Let `S` be a locally
Noetherian scheme contained in a big fppf site `B`, and let `F` and `G` be fppf sheaves on the big
fppf site of `S` which are limit preserving in the sense of Stacks 049J. Every transformation
between the restrictions of `F` and `G` to the locally Noetherian objects of the site is the
restriction of exactly one transformation `F ⟶ G`. -/
theorem existsUnique_hom_whiskerLeft_eq_bigFppfOver [IsLocallyNoetherian S]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hFs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hFl : LimitPreserving.{u, w, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F)
    (hGs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hGl : LimitPreserving.{u, w, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G)
    (σ : (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ F ⟶
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ G) :
    ∃! θ : F ⟶ G, Functor.whiskerLeft (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op θ = σ := by
  let R := liftToContainedOver.{w} B hS
  let hR := fullyFaithfulLiftToContainedOver.{w} B hS
  let R₂ := liftToContainedLocallyNoetherianOver.{w} B hS
  let hR₂ := fullyFaithfulLiftToContainedLocallyNoetherianOver.{w} B hS
  let h := isContainedLocallyNoetherianOver_le B (S := S)
  let ιN := ObjectProperty.ι (fun T : BigFppfOver B S hS =>
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))
  -- restriction to locally Noetherian objects commutes with the identifications
  have hcomm : ∀ {F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} (θ : F' ⟶ G'),
      R₂.map (Functor.whiskerLeft ιN.op θ) =
        Functor.whiskerLeft (ObjectProperty.ιOfLE h).op (R.map θ) := fun _ => rfl
  obtain ⟨θ₁, hθ₁, huniq₁⟩ := existsUnique_hom_whiskerLeft_ιOfLE_eq.{w} h
    (hasAffineOpens_isContainedOver B) (hasFinitePresentationAffines_isContainedOver B hS)
    (hasAffineOpens_isContainedLocallyNoetherianOver B)
    (hasFinitePresentationAffines_isContainedLocallyNoetherianOver B hS)
    (isZariskiSheafOnSubcategory_of_isSheaf B hS hFs)
    (preservesAffineLimitsOnSubcategory_of_limitPreserving B hS hFl)
    (isZariskiSheafOnSubcategory_of_isSheaf B hS hGs)
    (preservesAffineLimitsOnSubcategory_of_limitPreserving B hS hGl)
    (F := R.obj F) (G := R.obj G) (R₂.map σ)
  refine ⟨hR.preimage θ₁, hR₂.map_injective ?_, fun θ hθ => hR.map_injective ?_⟩
  · exact (hcomm _).trans ((congrArg (Functor.whiskerLeft (ObjectProperty.ιOfLE h).op)
      (hR.map_preimage θ₁)).trans hθ₁)
  · exact (huniq₁ _ ((hcomm θ).symm.trans (congrArg R₂.map hθ))).trans
      (hR.map_preimage θ₁).symm

/-- A transformation with an inverse after restriction along `K` has an inverse, if the identity
is the only transformation `H ⟶ H` restricting to the identity. -/
private theorem comp_eq_id_of_existsUnique_whiskerLeft {C D E : Type*} [Category C] [Category D]
    [Category E] {K : C ⥤ D} {H H' : D ⥤ E}
    (h : ∃! ψ : H ⟶ H, Functor.whiskerLeft K ψ = 𝟙 (K ⋙ H)) (θ : H ⟶ H') (θ' : H' ⟶ H)
    (hθ : Functor.whiskerLeft K θ ≫ Functor.whiskerLeft K θ' = 𝟙 (K ⋙ H)) : θ ≫ θ' = 𝟙 H :=
  let ⟨_, _, hu⟩ := h
  (hu _ (by beta_reduce; rw [Functor.whiskerLeft_comp, hθ])).trans
    (hu _ (Functor.whiskerLeft_id' _)).symm

/-- **An isomorphism on locally Noetherian objects extends uniquely.** Let `S` be a locally
Noetherian scheme contained in a big fppf site `B`, and let `F` and `G` be fppf sheaves on the big
fppf site of `S` which are limit preserving in the sense of Stacks 049J. Every isomorphism between
the restrictions of `F` and `G` to the locally Noetherian objects of the site is the restriction
of exactly one isomorphism `F ≅ G`. -/
theorem existsUnique_iso_isoWhiskerLeft_eq_bigFppfOver [IsLocallyNoetherian S]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hFs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hFl : LimitPreserving.{u, w, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F)
    (hGs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hGl : LimitPreserving.{u, w, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G)
    (e : (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ F ≅
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ G) :
    ∃! e' : F ≅ G, Functor.isoWhiskerLeft (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op e' = e := by
  obtain ⟨θ, hθ, huθ⟩ := existsUnique_hom_whiskerLeft_eq_bigFppfOver B hS hFs hFl hGs hGl e.hom
  obtain ⟨θ', hθ', _⟩ := existsUnique_hom_whiskerLeft_eq_bigFppfOver B hS hGs hGl hFs hFl e.inv
  have h₁ := comp_eq_id_of_existsUnique_whiskerLeft
    (existsUnique_hom_whiskerLeft_eq_bigFppfOver B hS hFs hFl hFs hFl (𝟙 _)) θ θ'
    (by rw [hθ, hθ', e.hom_inv_id])
  have h₂ := comp_eq_id_of_existsUnique_whiskerLeft
    (existsUnique_hom_whiskerLeft_eq_bigFppfOver B hS hGs hGl hGs hGl (𝟙 _)) θ' θ
    (by rw [hθ, hθ', e.inv_hom_id])
  refine ⟨⟨θ, θ', h₁, h₂⟩, Iso.ext hθ, fun e' he' => Iso.ext (huθ _ ?_)⟩
  exact congrArg Iso.hom he'

end AlgebraicGeometry.ExtendingFunctors

end
