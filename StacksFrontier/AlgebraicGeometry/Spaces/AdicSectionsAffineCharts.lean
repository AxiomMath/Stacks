module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# The affine charts suffice for a bijection on the inverse limits of the sections

Let `F` be an algebraic space over a scheme `S` of a big fppf site `B`, let `P`, `Q` be inverse
systems of `𝒪_F`-modules presented by their successor transitions and let `β : P ⟶ Q` be a
morphism of inverse systems.  If `β` is bijective on the inverse limits of the sections over
every étale chart whose scheme is *affine*, then it is bijective on the inverse limits of the
sections over *every* étale chart.

## Main definitions

* `AlgebraicGeometry.Space.adicSectionsRestrict` — restriction of a compatible sequence of
  sections along a morphism of charts.

## Main results

* `AlgebraicGeometry.Space.injective_adicSectionsMapAt_of_isAffine` — **injectivity over the
  affine charts gives injectivity over every chart.**
* `AlgebraicGeometry.Space.surjective_adicSectionsMapAt_of_isAffine` — **bijectivity over the
  affine charts gives surjectivity over every chart.**
* `AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_isAffine` — **bijectivity over the
  affine charts gives bijectivity over every chart.**

## Implementation notes

The charts are written `op U` for `U` an object of `AlgebraicGeometry.Space.SmallEtale` rather
than as an arbitrary object of `((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ`, which is the same
thing: `AlgebraicGeometry.Space.smallEtaleRingedSite` is a `def`, so its `C` projection is not
reduced at reducible transparency, and a chart presented as `U.unop` makes the restriction maps
of the sheaves print — and match, under `rw` — at `op U.unop` instead of at `U`.  The last
statement is the one in the `∀ U` form.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (P Q : ℕ → Modules.{u, m} B S hS F hF) (trP : ∀ n, P (n + 1) ⟶ P n)
    (trQ : ∀ n, Q (n + 1) ⟶ Q n) (β : ∀ n : ℕ, P n ⟶ Q n)
    (hβ : ∀ n : ℕ, trP n ≫ β n = β (n + 1) ≫ trQ n)

/-! ### Restriction of a compatible sequence of sections -/

/-- **Restriction of a compatible sequence of sections along a morphism of charts**, term by
term. -/
def adicSectionsRestrict {U V : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (g : U ⟶ V)
    (t : adicSectionsAt B S hS F hF P trP U) : adicSectionsAt B S hS F hF P trP V :=
  ⟨fun n => (P n).val.map g (t.1 n), fun n => by
    rw [PresheafOfModules.naturality_apply (trP n).val g, t.2 n]⟩

/-- Restriction along a composite is the composite of the restrictions. -/
theorem adicSectionsRestrict_comp
    {U V W : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (g : U ⟶ V) (g' : V ⟶ W)
    (t : adicSectionsAt B S hS F hF P trP U) :
    adicSectionsRestrict B S hS F hF P trP (g ≫ g') t =
      adicSectionsRestrict B S hS F hF P trP g'
        (adicSectionsRestrict B S hS F hF P trP g t) :=
  Subtype.ext (funext fun n => PresheafOfModules.map_comp_apply (P n).val g g' (t.1 n))

/-- **A morphism of inverse systems commutes with restriction on the inverse limits of the
sections.** -/
theorem adicSectionsMapAt_adicSectionsRestrict
    {U V : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (g : U ⟶ V)
    (t : adicSectionsAt B S hS F hF P trP U) :
    adicSectionsMapAt B S hS F hF P Q trP trQ β hβ V
        (adicSectionsRestrict B S hS F hF P trP g t) =
      adicSectionsRestrict B S hS F hF Q trQ g
        (adicSectionsMapAt B S hS F hF P Q trP trQ β hβ U t) :=
  Subtype.ext (funext fun n => PresheafOfModules.naturality_apply (β n).val g (t.1 n))

/-! ### From the affine charts to all charts -/

/-- Two sections of a sheaf of modules over a chart which agree after restriction along the
members of an étale covering family by charts are equal. -/
private theorem eq_of_map_ofArrows_eq {I : Type (u + 1)} {Z : I → SmallEtale B S hS F}
    {U : SmallEtale B S hS F} {a : ∀ i, Z i ⟶ U}
    (hcov : Sieve.ofArrows Z a ∈ SmallEtale.topology B S hS F U) (N : Modules B S hS F hF)
    {x y : N.val.obj (op U)} (h : ∀ i, N.val.map (a i).op x = N.val.map (a i).op y) : x = y := by
  refine ((Presieve.isSeparatedFor_iff_generate (R := Presieve.ofArrows Z a)).2
    (Stacks.SheafOfModules.isSeparated_presheaf N _ hcov)).ext ?_
  rintro T f ⟨i⟩
  exact h i

/-- **Injectivity on the inverse limits of the sections over the affine charts gives injectivity
over every chart.** -/
theorem injective_adicSectionsMapAt_of_isAffine
    (hinj : ∀ W : SmallEtale B S hS F, IsAffine (chartScheme W) →
      Function.Injective (adicSectionsMapAt B S hS F hF P Q trP trQ β hβ (op W)))
    (U : SmallEtale B S hS F) :
    Function.Injective (adicSectionsMapAt B S hS F hF P Q trP trQ β hβ (op U)) := by
  intro t t' h
  obtain ⟨I, Z, a, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F U
  have key : ∀ i : I, adicSectionsRestrict B S hS F hF P trP (a i).op t =
      adicSectionsRestrict B S hS F hF P trP (a i).op t' := fun i =>
    hinj (Z i) (haff i)
      ((adicSectionsMapAt_adicSectionsRestrict B S hS F hF P Q trP trQ β hβ (a i).op t).trans
        ((congrArg (adicSectionsRestrict B S hS F hF Q trQ (a i).op) h).trans
          (adicSectionsMapAt_adicSectionsRestrict B S hS F hF P Q trP trQ β hβ
            (a i).op t').symm))
  refine Subtype.ext (funext fun n => eq_of_map_ofArrows_eq B S hS F hF hcov (P n) fun i => ?_)
  exact congrArg (fun z : adicSectionsAt B S hS F hF P trP (op (Z i)) => z.1 n) (key i)

/-- **Bijectivity on the inverse limits of the sections over the affine charts gives surjectivity
over every chart.** -/
theorem surjective_adicSectionsMapAt_of_isAffine
    (hbij : ∀ W : SmallEtale B S hS F, IsAffine (chartScheme W) →
      Function.Bijective (adicSectionsMapAt B S hS F hF P Q trP trQ β hβ (op W)))
    (U : SmallEtale B S hS F) :
    Function.Surjective (adicSectionsMapAt B S hS F hF P Q trP trQ β hβ (op U)) := by
  intro t'
  obtain ⟨I, Z, a, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F U
  choose s hs using fun i : I => (hbij (Z i) (haff i)).2
    (adicSectionsRestrict B S hS F hF Q trQ (a i).op t')
  have hinj := injective_adicSectionsMapAt_of_isAffine B S hS F hF P Q trP trQ β hβ
    (fun W hW => (hbij W hW).1)
  have hpull : ∀ (i : I) (T : SmallEtale B S hS F) (g : T ⟶ Z i),
      adicSectionsMapAt B S hS F hF P Q trP trQ β hβ (op T)
          (adicSectionsRestrict B S hS F hF P trP g.op (s i)) =
        adicSectionsRestrict B S hS F hF Q trQ ((a i).op ≫ g.op) t' := fun i T g =>
    (adicSectionsMapAt_adicSectionsRestrict B S hS F hF P Q trP trQ β hβ g.op (s i)).trans
      ((congrArg (adicSectionsRestrict B S hS F hF Q trQ g.op) (hs i)).trans
        (adicSectionsRestrict_comp B S hS F hF Q trQ (a i).op g.op t').symm)
  have hcompat : ∀ (i j : I) (T : SmallEtale B S hS F) (gi : T ⟶ Z i) (gj : T ⟶ Z j),
      gi ≫ a i = gj ≫ a j →
      adicSectionsRestrict B S hS F hF P trP gi.op (s i) =
        adicSectionsRestrict B S hS F hF P trP gj.op (s j) := fun i j T gi gj hg =>
    hinj T ((hpull i T gi).trans ((congrArg (fun k : T ⟶ U =>
      adicSectionsRestrict B S hS F hF Q trQ k.op t') hg).trans (hpull j T gj).symm))
  have hsf : ∀ n : ℕ, Presieve.IsSheafFor
      ((P n).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
      (Presieve.ofArrows Z a) := fun n =>
    (Presieve.isSheafFor_iff_generate _).2
      (Stacks.SheafOfModules.ImageSubsheaf.isSheaf_forget (P n) _ hcov)
  have hex : ∀ n : ℕ, ∃ x : (P n).val.obj (op U),
      ∀ i : I, (P n).val.map (a i).op x = (s i).1 n := fun n =>
    ((Presieve.isSheafFor_arrows_iff _ _).1 (hsf n) (fun i => (s i).1 n)
      (fun i j T gi gj hg =>
        congrArg (fun z : adicSectionsAt B S hS F hF P trP (op T) => z.1 n)
          (hcompat i j T gi gj hg))).exists
  choose x hx using hex
  have hcomp : ∀ n : ℕ, (trP n).val.app (op U) (x (n + 1)) = x n := by
    intro n
    refine eq_of_map_ofArrows_eq B S hS F hF hcov (P n) fun i => ?_
    refine (PresheafOfModules.naturality_apply (trP n).val (a i).op _).symm.trans ?_
    rw [hx (n + 1) i]
    exact ((s i).2 n).trans (hx n i).symm
  refine ⟨⟨x, hcomp⟩, Subtype.ext (funext fun n => ?_)⟩
  refine ((Presieve.isSeparatedFor_iff_generate (R := Presieve.ofArrows Z a)).2
    (Stacks.SheafOfModules.isSeparated_presheaf (Q n) _ hcov)).ext ?_
  rintro T f ⟨i⟩
  refine (PresheafOfModules.naturality_apply (β n).val (a i).op _).symm.trans ?_
  rw [hx n i]
  exact congrArg (fun z : adicSectionsAt B S hS F hF Q trQ (op (Z i)) => z.1 n) (hs i)

/-- **Bijectivity on the inverse limits of the sections over the affine charts gives bijectivity
over every chart.** -/
theorem bijective_adicSectionsMapAt_of_isAffine
    (hbij : ∀ W : SmallEtale B S hS F, IsAffine (chartScheme W) →
      Function.Bijective (adicSectionsMapAt B S hS F hF P Q trP trQ β hβ (op W)))
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) :
    Function.Bijective (adicSectionsMapAt B S hS F hF P Q trP trQ β hβ U) := by
  obtain ⟨U⟩ := U
  exact ⟨injective_adicSectionsMapAt_of_isAffine B S hS F hF P Q trP trQ β hβ
      (fun W hW => (hbij W hW).1) U,
    surjective_adicSectionsMapAt_of_isAffine B S hS F hF P Q trP trQ β hβ hbij U⟩

end AlgebraicGeometry.Space

end
