module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing

/-!
# The right derived functors of a sheaf-valued functor are sheafified presheaf-valued ones

Let `P : Sh(𝒞, 𝒜) ⥤ Sh(𝒟, 𝒜)` be *any* additive functor into a category of sheaves.  Composing it
with the inclusion of sheaves into presheaves gives `P^pre : Sh(𝒞, 𝒜) ⥤ PSh(𝒟, 𝒜)`, and `P` is
recovered from `P^pre` by sheafification, the counit of `a ⊣ forget` being invertible on sheaves.
Sheafification is exact, so it comes out of a right derived functor, and therefore

`R^p P ≅ (R^p P^pre) ⋙ a`

for every `p`.  The value of `R^p P^pre` at an object `V` of `𝒟` is `R^p` of the functor
`F ↦ (P F)(V)`, evaluation at `V` being exact as well.  Taken together, these two facts turn the
vanishing of `R^p P` into a *local* question about the functors `F ↦ (P F)(V)`, one object at a
time: if every object of `𝒟` has a covering sieve along whose members those derived functors
vanish, then `R^p P F = 0`.

This is the pattern of
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/AbelianHigherDirectImageSheafification.lean`,
which runs it for the direct image along a *continuous* functor of sites, where `P^pre` is the
cohomology presheaf `V ↦ F(u V)` of [Stacks, Tag 072W].  Nothing in the pattern uses that `P` is
such a direct image: `P` is an arbitrary additive functor here, so the same criterion applies to a
direct image built as a right Kan extension along a *cocontinuous* functor — the shape
`CategoryTheory.Functor.sheafPushforwardCocontinuous` has, and the one a morphism of topoi coming
from [Stacks, Tag 00XL] has.

## Main results

All in the namespace `Stacks.Cohomology.SheafifiedDerivedFunctor`.

* `presheafPartCompSheafification` — `P^pre ⋙ a ≅ P`.
* `rightDerivedPresheafPartIso` — `R^p P ≅ (R^p P^pre) ⋙ a`.
* `presheafPartEvaluationIso` — the value of `R^p P^pre` at `V` is `R^p (F ↦ (P F)(V))`.
* `isZero_rightDerived_of_isZero_sheafify` — `R^p P F = 0` as soon as `R^p P^pre F` sheafifies to
  zero.
* `isZero_rightDerived_of_locallyIsZero` — **the criterion**: `R^p P F = 0` as soon as every
  object of `𝒟` has a covering presieve along whose members `R^p (F ↦ (P F)(-))` vanishes at `F`.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.SheafifiedDerivedFunctor

universe t v₁ u₁ v₂ u₂

section General

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (A : Type*) [Category* A] [Abelian A] [HasSheafify J A] [HasSheafify K A]
  (P : Sheaf K A ⥤ Sheaf J A) [P.Additive]

/-- **The presheaf-valued form of a sheaf-valued functor**: `F ↦ (P F)` read as a presheaf on
`𝒟`.  Its `p`-th right derived functor sheafifies to `R^p P`. -/
def presheafPart : Sheaf K A ⥤ (Dᵒᵖ ⥤ A) :=
  P ⋙ sheafToPresheaf J A

/-- The presheaf-valued form of an additive functor is again additive: it is the composite of `P`
with the inclusion of sheaves into presheaves, which is additive. -/
instance additive_presheafPart : (presheafPart A P).Additive :=
  inferInstanceAs (P ⋙ sheafToPresheaf J A).Additive

/-- The presheaf-valued form, evaluated at an object `V` of `𝒟`, is the functor `F ↦ (P F)(V)`;
this holds by definition. -/
theorem presheafPart_comp_evaluation (V : D) :
    presheafPart (J := J) A P ⋙ (evaluation Dᵒᵖ A).obj (op V) =
      P ⋙ (sheafSections J A).obj (op V) :=
  rfl

/-- **Sheafifying the presheaf-valued form returns `P`**: the presheaf underlying `P F` is already
a sheaf, so the counit of `a ⊣ forget` is invertible there. -/
def presheafPartCompSheafification :
    presheafPart (J := J) A P ⋙ presheafToSheaf J A ≅ P :=
  Functor.isoWhiskerLeft P (asIso (sheafificationAdjunction J A).counit) ≪≫ P.rightUnitor

attribute [local instance] SheafifiedHigherDirectImage.preservesHomology_presheafToSheaf

variable [EnoughInjectives (Sheaf K A)]

/-- **`R^p P ≅ (R^p P^pre) ⋙ a`**: the `p`-th right derived functor of a sheaf-valued functor is
the sheafification of the `p`-th right derived functor of its presheaf-valued form.  The exact
functor `a` comes out of the right derived functor by
`CategoryTheory.Functor.rightDerivedCompIso`. -/
def rightDerivedPresheafPartIso (p : ℕ) :
    P.rightDerived p ≅ (presheafPart (J := J) A P).rightDerived p ⋙ presheafToSheaf J A :=
  (Functor.rightDerivedIsoOfNatIso (presheafPartCompSheafification A P) p).symm ≪≫
    Functor.rightDerivedCompIso (presheafPart (J := J) A P) (presheafToSheaf J A) p

/-- **The value of `R^p P^pre` at an object `V` of `𝒟` is `R^p` of `F ↦ (P F)(V)`**, evaluation
at `V` being exact. -/
def presheafPartEvaluationIso (p : ℕ) (V : D) :
    (presheafPart (J := J) A P ⋙ (evaluation Dᵒᵖ A).obj (op V)).rightDerived p ≅
      (presheafPart (J := J) A P).rightDerived p ⋙ (evaluation Dᵒᵖ A).obj (op V) :=
  letI : ((evaluation Dᵒᵖ A).obj (op V)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  Functor.rightDerivedCompIso (presheafPart (J := J) A P) ((evaluation Dᵒᵖ A).obj (op V)) p

/-- **`R^p P F = 0` as soon as `R^p P^pre F` sheafifies to zero.**  This is the vanishing criterion
`R^p P ≅ (R^p P^pre) ⋙ a` gives. -/
theorem isZero_rightDerived_of_isZero_sheafify (p : ℕ) (F : Sheaf K A)
    (h : IsZero ((presheafToSheaf J A).obj
      (((presheafPart (J := J) A P).rightDerived p).obj F))) :
    IsZero ((P.rightDerived p).obj F) :=
  IsZero.of_iso h ((rightDerivedPresheafPartIso A P p).app F)

end General

section AddCommGrp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (P : Sheaf K AddCommGrpCat.{t} ⥤ Sheaf J AddCommGrpCat.{t}) [P.Additive]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{t})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{t})]

/-- **The local vanishing criterion for the right derived functors of a sheaf-valued functor.**
If every object `V` of `𝒟` admits a covering *presieve* such that, for every member `W ⟶ V` of it,
the `p`-th right derived functor of `F ↦ (P F)(W)` vanishes at `F`, then `R^p P F = 0`.

The hypothesis is about one object at a time: no naturality in `W` is involved, because the
section of the `p`-th cohomology presheaf being restricted lands in a zero object whatever the
restriction map is.

It is a *presieve* and not a sieve for the reason recorded in the documentation of
`CategoryTheory.GrothendieckTopology.IsCoveringFamily`: a covering sieve contains every morphism
factoring through a member, so the sources of its members never all satisfy a property — such as
affineness — that is not inherited by arbitrary subobjects.  Nothing is lost, the sieve of
morphisms along which a section dies being closed under precomposition. -/
theorem isZero_rightDerived_of_locallyIsZero (p : ℕ) (F : Sheaf K AddCommGrpCat.{t})
    (h : ∀ V : D, ∃ R : Presieve V, Sieve.generate R ∈ J V ∧ ∀ ⦃W : D⦄ (f : W ⟶ V), R f →
      IsZero (((presheafPart (J := J) AddCommGrpCat.{t} P ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{t}).obj (op W)).rightDerived p).obj F)) :
    IsZero ((P.rightDerived p).obj F) := by
  refine isZero_rightDerived_of_isZero_sheafify AddCommGrpCat.{t} P p F
    (SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero J _ fun V x ↦ ?_)
  obtain ⟨R, hR, hzero⟩ := h V
  refine J.superset_covering ?_ hR
  rintro W f ⟨Z, g, k, hk, rfl⟩
  refine Sieve.downward_closed _ ?_ g
  have hZ : IsZero ((((presheafPart (J := J) AddCommGrpCat.{t} P).rightDerived p).obj F).obj
      (op Z)) :=
    IsZero.of_iso (hzero k hk)
      ((presheafPartEvaluationIso AddCommGrpCat.{t} P p Z).app F).symm
  show (((presheafPart (J := J) AddCommGrpCat.{t} P).rightDerived p).obj F).map k.op x =
    (((presheafPart (J := J) AddCommGrpCat.{t} P).rightDerived p).obj F).map k.op 0
  exact (AddCommGrpCat.subsingleton_of_isZero hZ).elim _ _

end AddCommGrp

end Stacks.Cohomology.SheafifiedDerivedFunctor

end
