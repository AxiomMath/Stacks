module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineInterchange
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSubcategorySheaf

/-!
# Restricting limit preserving sheaves to a full subcategory of schemes over a base

Let `S` be a scheme, let `τ` be one of the five topologies of
`AlgebraicGeometry.CoveringTopology` and let `𝒞` be a full subcategory of `Sch/S` satisfying the
conditions (1) and (2) of Stacks 0EUW.
Restriction along the inclusion `𝒞 → Sch/S` carries a limit preserving sheaf on `(Sch/S)_τ` to a
functor on `𝒞`, and this file shows that every limit preserving sheaf on the site `(𝒞)_τ` arises
this way: it is the restriction of the extension of Stacks 0EUW, which is a sheaf for `τ` by
Stacks 0GDW.

Together with the faithfulness supplied by
`AlgebraicGeometry.ExtendingFunctors.hom_ext_of_app_eq_on_subcategory` this is the essential
surjectivity half of Stacks 0GE3 for the locally Noetherian subcategory.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.IsLimitPreservingSheaf`: a functor on `Sch/S` which is a
  sheaf for `τ` and carries directed inverse limits of affine schemes over `S` to filtered
  colimits.
* `AlgebraicGeometry.ExtendingFunctors.IsLimitPreservingSheafOnSubcategory`: the same two
  conditions for a functor on the full subcategory, the sheaf condition being taken for the site
  `(𝒞)_τ`.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.exists_isLimitPreservingSheaf_restriction`: every limit
  preserving sheaf on `(𝒞)_τ` is the restriction of a limit preserving sheaf on `(Sch/S)_τ`.
* `AlgebraicGeometry.ExtendingFunctors.exists_isLimitPreservingSheaf_restriction_noetherian`: the
  same for the locally Noetherian subcategory of `Sch/S` over a locally Noetherian base, which is
  the essential surjectivity half of Stacks 0GE3.

## Implementation notes

"Limit preserving" is read, as in the source, as carrying a directed inverse limit of *affine*
objects to a filtered colimit; on the subcategory this is
`AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimitsOnSubcategory`, the condition (b) of
Stacks 0EUW, and on `Sch/S` it is
`AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimits`.

The value universe is `Type (max w (u + 1))`, which is where the extension of Stacks 0EUW takes
its values: the index category of the colimit computing it has objects in `Type (u + 1)`.
Coverings are indexed by types in the universe `u` of the schemes.

## References

* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 0GDW](https://stacks.math.columbia.edu/tag/0GDW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}}

/-! ### Limit preserving sheaves -/

/-- A **limit preserving sheaf on `(Sch/S)_τ`**: a functor on `Sch/S` which satisfies the sheaf
condition for every `τ`-covering and carries a directed inverse limit of affine schemes over `S`
to a filtered colimit. -/
def IsLimitPreservingSheaf (τ : CoveringTopology) :
    ObjectProperty ((Over S)ᵒᵖ ⥤ Type (max w (u + 1))) :=
  fun G => IsCoveringSheaf.{max w (u + 1), u, u} τ G ∧ PreservesAffineLimits G

/-- A **limit preserving sheaf on the site `(𝒞)_τ`**: a functor on the full subcategory which
satisfies the sheaf condition for every `τ`-covering by objects of the subcategory and carries a
directed inverse limit of affine objects of the subcategory to a filtered colimit. The second
condition is condition (b) of Stacks 0EUW. -/
def IsLimitPreservingSheafOnSubcategory (τ : CoveringTopology) (P : ObjectProperty (Over S)) :
    ObjectProperty (P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) :=
  fun F => IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} τ P F ∧
    PreservesAffineLimitsOnSubcategory P F

/-! ### Essential surjectivity of the restriction -/

/-- **Every limit preserving sheaf on `(𝒞)_τ` is a restriction.** Let `𝒞` be a full subcategory of
`Sch/S` satisfying conditions (1) and (2) of Stacks 0EUW. A functor on `𝒞` which is a sheaf for
the `τ`-coverings by objects of `𝒞` and carries directed inverse limits of affine objects to
filtered colimits satisfies conditions (a), (b) and (c) of Stacks 0GDW, so its extension of Stacks
0EUW is a limit preserving sheaf on `(Sch/S)_τ` restricting to it. -/
theorem exists_isLimitPreservingSheaf_restriction (τ : CoveringTopology)
    {P : ObjectProperty (Over S)} (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P)
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hF : IsLimitPreservingSheafOnSubcategory τ P F) :
    ∃ G : (Over S)ᵒᵖ ⥤ Type (max w (u + 1)),
      IsLimitPreservingSheaf τ G ∧ Nonempty (P.ι.op ⋙ G ≅ F) := by
  obtain ⟨hsF, hbF⟩ := hF
  have haF : IsZariskiSheafOnSubcategory P F :=
    isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory τ hP1 hsF
  have hcF : IsStandardAffineSheafOnSubcategory.{max w (u + 1), u, u} τ P F :=
    isStandardAffineSheafOnSubcategory_of_isCoveringSheafOnSubcategory τ hsF
  exact ⟨extension P F,
    ⟨isCoveringSheaf_extension_of_isStandardAffineSheafOnSubcategory τ P F hP1 hP2 haF hbF hcF,
      preservesAffineLimits_extension F hP1 hP2 haF⟩,
    nonempty_restrictionIso F hP1 hP2 haF hbF⟩

/-- **Essential surjectivity of the restriction functor of Stacks 0GE3.** For a locally Noetherian
scheme `S`, every limit preserving sheaf on the site `(Noetherian/S)_τ` is the restriction of a
limit preserving sheaf on `(Sch/S)_τ`. -/
theorem exists_isLimitPreservingSheaf_restriction_noetherian (τ : CoveringTopology)
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (IsLocallyNoetherianOver (S := S)).FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hF : IsLimitPreservingSheafOnSubcategory τ (IsLocallyNoetherianOver (S := S)) F) :
    ∃ G : (Over S)ᵒᵖ ⥤ Type (max w (u + 1)), IsLimitPreservingSheaf τ G ∧
      Nonempty ((IsLocallyNoetherianOver (S := S)).ι.op ⋙ G ≅ F) :=
  exists_isLimitPreservingSheaf_restriction τ hasAffineOpens_isLocallyNoetherianOver
    hasFinitePresentationAffines_isLocallyNoetherianOver F hF

/-! ### The restriction functor -/

/-- The restriction of a limit preserving sheaf on `(Sch/S)_τ` to the full subcategory is a limit
preserving sheaf on the site `(𝒞)_τ`. -/
theorem isLimitPreservingSheafOnSubcategory_restriction (τ : CoveringTopology)
    {P : ObjectProperty (Over S)} (hPp : HasCoveringPullbacks τ P)
    {G : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} (hG : IsLimitPreservingSheaf τ G) :
    IsLimitPreservingSheafOnSubcategory τ P (P.ι.op ⋙ G) :=
  ⟨isCoveringSheafOnSubcategory_of_isCoveringSheaf τ hPp hG.1,
    preservesAffineLimitsOnSubcategory_of_preservesAffineLimits hG.2⟩

/-- **The restriction functor of Stacks 0GE3.** Restriction along the inclusion of the full
subcategory, from the limit preserving sheaves on `(Sch/S)_τ` to the limit preserving sheaves on
the site `(𝒞)_τ`. -/
def limitPreservingRestriction (τ : CoveringTopology) {P : ObjectProperty (Over S)}
    (hPp : HasCoveringPullbacks τ P) :
    (IsLimitPreservingSheaf (S := S) τ).FullSubcategory ⥤
      (IsLimitPreservingSheafOnSubcategory τ P).FullSubcategory :=
  ObjectProperty.lift _
    ((IsLimitPreservingSheaf (S := S) τ).ι ⋙ (Functor.whiskeringLeft _ _ _).obj P.ι.op)
    fun G => isLimitPreservingSheafOnSubcategory_restriction τ hPp G.property

/-- The underlying functor of the restriction of `G` is `G.obj` precomposed with the inclusion of
the full subcategory. -/
@[simp]
lemma limitPreservingRestriction_obj_obj (τ : CoveringTopology) {P : ObjectProperty (Over S)}
    (hPp : HasCoveringPullbacks τ P) (G : (IsLimitPreservingSheaf (S := S) τ).FullSubcategory) :
    ((limitPreservingRestriction τ hPp).obj G).obj = P.ι.op ⋙ G.obj := rfl

/-- The underlying natural transformation of the restriction of `θ` is the whiskering of `θ.hom`
by the inclusion of the full subcategory. -/
@[simp]
lemma limitPreservingRestriction_map_hom (τ : CoveringTopology) {P : ObjectProperty (Over S)}
    (hPp : HasCoveringPullbacks τ P)
    {G₁ G₂ : (IsLimitPreservingSheaf (S := S) τ).FullSubcategory} (θ : G₁ ⟶ G₂) :
    ((limitPreservingRestriction τ hPp).map θ).hom
      = Functor.whiskerLeft P.ι.op θ.hom := rfl

/-- **Faithfulness of the restriction functor of Stacks 0GE3.** A morphism of limit preserving
sheaves on `(Sch/S)_τ` is determined by its restriction to the full subcategory: this is the sharp
uniqueness statement of Stacks 0EUW, which needs only condition (2) on the subcategory, the
Zariski sheaf condition on the target and the limit condition on the source. -/
theorem faithful_limitPreservingRestriction (τ : CoveringTopology) {P : ObjectProperty (Over S)}
    (hP2 : HasFinitePresentationAffines P) (hPp : HasCoveringPullbacks τ P) :
    (limitPreservingRestriction τ hPp).Faithful where
  map_injective := by
    intro G₁ G₂ θ θ' hθ
    have hw : ((limitPreservingRestriction τ hPp).map θ).hom
        = ((limitPreservingRestriction τ hPp).map θ').hom :=
      congrArg InducedCategory.Hom.hom hθ
    refine ObjectProperty.hom_ext _ (hom_ext_of_app_eq_on_subcategory hP2 G₁.property.2
      (isZariskiSheaf_of_isCoveringSheaf τ G₂.property.1) θ.hom θ'.hom fun Y hY => ?_)
    exact congrArg (fun γ : P.ι.op ⋙ G₁.obj ⟶ P.ι.op ⋙ G₂.obj =>
      γ.app (op (⟨Y, hY⟩ : P.FullSubcategory))) hw

/-- **Essential surjectivity of the restriction functor of Stacks 0GE3.** Every limit preserving
sheaf on the site `(𝒞)_τ` is isomorphic to the restriction of a limit preserving sheaf on
`(Sch/S)_τ`, namely to the restriction of the extension of Stacks 0EUW. -/
theorem essSurj_limitPreservingRestriction (τ : CoveringTopology) {P : ObjectProperty (Over S)}
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (hPp : HasCoveringPullbacks τ P) :
    (limitPreservingRestriction τ hPp).EssSurj where
  mem_essImage F := by
    obtain ⟨G, hG, ⟨e⟩⟩ :=
      exists_isLimitPreservingSheaf_restriction τ hP1 hP2 F.obj F.property
    exact ⟨⟨G, hG⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso e⟩⟩

/-- **Faithfulness of the restriction functor of Stacks 0GE3** for the locally Noetherian
subcategory of a locally Noetherian base. -/
theorem faithful_limitPreservingRestriction_noetherian (τ : CoveringTopology) {S : Scheme.{u}}
    [IsLocallyNoetherian S] :
    (limitPreservingRestriction (P := IsLocallyNoetherianOver (S := S)) τ
      (hasCoveringPullbacks_isLocallyNoetherianOver τ)).Faithful :=
  faithful_limitPreservingRestriction τ hasFinitePresentationAffines_isLocallyNoetherianOver _

/-- **Essential surjectivity of the restriction functor of Stacks 0GE3** for the locally Noetherian
subcategory of a locally Noetherian base. -/
theorem essSurj_limitPreservingRestriction_noetherian (τ : CoveringTopology) {S : Scheme.{u}}
    [IsLocallyNoetherian S] :
    (limitPreservingRestriction (P := IsLocallyNoetherianOver (S := S)) τ
      (hasCoveringPullbacks_isLocallyNoetherianOver τ)).EssSurj :=
  essSurj_limitPreservingRestriction τ hasAffineOpens_isLocallyNoetherianOver
    hasFinitePresentationAffines_isLocallyNoetherianOver _

end AlgebraicGeometry.ExtendingFunctors

end
