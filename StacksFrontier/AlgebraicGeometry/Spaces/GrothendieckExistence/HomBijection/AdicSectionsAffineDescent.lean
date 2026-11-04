module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison

/-!
# Inverse limits of sections over the affine charts determine those over every chart

Let `F` be an algebraic space and let `P` be a sheaf of types on the small étale site of `F`.
The étale charts of `F` with affine source cover every chart
(`AlgebraicGeometry.Space.SmallEtale.isCoverDense_affineEtaleInclusion`), so a section of `P` is
determined by its restrictions to the affine charts over it, and a family of sections over the
affine charts over a chart `U` which agrees on every affine chart mapping to two of them glues to a
section over `U`.

Applied to the terms of two inverse systems of `𝒪_F`-modules, this shows that a morphism of
inverse systems which is bijective on the inverse limits of the sections over every affine chart is
bijective on the inverse limits of the sections over every chart: the hypothesis `h0882` of
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv` need only be checked on affine charts.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.C1573.eq_of_forall_isAffine`: separation along affine charts.
* `AlgebraicGeometry.Space.SmallEtale.C1573.exists_eq_of_forall_isAffine`: gluing along affine
  charts.
* `AlgebraicGeometry.Space.C1573.bijective_adicSectionsMapAt_of_bijective_affineCharts`: the
  reduction of `h0882` to affine charts.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w m u

namespace AlgebraicGeometry.Space.SmallEtale.C1573

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

include hF in
/-- **Separation along affine charts.**  Two sections of a sheaf of types on the small étale site
over a chart `U` which agree on every affine chart over `U` are equal. -/
theorem eq_of_forall_isAffine {P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (topology B S hS F) P) {U : SmallEtale B S hS F}
    {x y : P.obj (op U)}
    (h : ∀ (V : SmallEtale B S hS F) (g : V ⟶ U), IsAffine (chartScheme V) →
      P.map g.op x = P.map g.op y) : x = y := by
  refine (hP _ ((isCoverDense_affineEtaleInclusion B S hS F hF).is_cover U)).isSeparatedFor.ext
    fun W f hf => ?_
  obtain ⟨⟨A, lift, map, fac⟩⟩ := hf
  rw [← fac, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
    h _ map A.property]

include hF in
/-- **Gluing along affine charts.**  A family of sections of a sheaf of types on the small étale
site over the affine charts over a chart `U`, which agrees on every affine chart mapping to two
members of the family compatibly with their maps to `U`, is the family of restrictions of a
section over `U`. -/
theorem exists_eq_of_forall_isAffine {P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (topology B S hS F) P) {U : SmallEtale B S hS F}
    (x : ∀ (V : SmallEtale B S hS F) (_ : V ⟶ U), IsAffine (chartScheme V) → P.obj (op V))
    (hx : ∀ (V₁ V₂ : SmallEtale B S hS F) (g₁ : V₁ ⟶ U) (g₂ : V₂ ⟶ U)
      (h₁ : IsAffine (chartScheme V₁)) (h₂ : IsAffine (chartScheme V₂))
      (W : SmallEtale B S hS F) (_ : IsAffine (chartScheme W)) (a₁ : W ⟶ V₁) (a₂ : W ⟶ V₂),
      a₁ ≫ g₁ = a₂ ≫ g₂ → P.map a₁.op (x V₁ g₁ h₁) = P.map a₂.op (x V₂ g₂ h₂)) :
    ∃ t : P.obj (op U), ∀ (V : SmallEtale B S hS F) (g : V ⟶ U)
      (h : IsAffine (chartScheme V)), P.map g.op t = x V g h := by
  have hcov := (isCoverDense_affineEtaleInclusion B S hS F hF).is_cover U
  let T := Sieve.coverByImage (AffineEtale.inclusion B S hS F) U
  let fam : Presieve.FamilyOfElements P T.arrows := fun W f hf =>
    P.map hf.some.lift.op (x _ hf.some.map hf.some.obj.property)
  have hcomp : fam.Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hc
    refine eq_of_forall_isAffine B S hS F hF hP fun V c hV => ?_
    simp only [fam, ← Functor.map_comp_apply, ← op_comp]
    refine hx _ _ _ _ _ _ V hV _ _ ?_
    rw [Category.assoc, Category.assoc, h₁.some.fac, Category.assoc, Category.assoc,
      h₂.some.fac, hc]
  refine ⟨(hP _ hcov).amalgamate fam hcomp, fun V g h => ?_⟩
  have hg : T.arrows g := ⟨{ obj := ⟨V, h⟩, lift := 𝟙 V, map := g }⟩
  rw [(hP _ hcov).valid_glue hcomp g hg]
  have := hx _ _ _ _ hg.some.obj.property h V h hg.some.lift (𝟙 V)
    (by rw [hg.some.fac, Category.id_comp])
  rw [op_id, Functor.map_id_apply] at this
  exact this

end AlgebraicGeometry.Space.SmallEtale.C1573

namespace AlgebraicGeometry.Space.C1573

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

section Sections

variable (X Y : ℕ → Modules.{u, m} B S hS F hF) (trX : ∀ n, X (n + 1) ⟶ X n)
    (trY : ∀ n, Y (n + 1) ⟶ Y n)

/-- The restriction of a compatible family of sections along a morphism of charts. -/
def adicSectionsRes {U V : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (g : U ⟶ V)
    (t : adicSectionsAt B S hS F hF X trX U) : adicSectionsAt B S hS F hF X trX V :=
  ⟨fun n => (X n).val.map g (t.1 n), fun n => by
    rw [PresheafOfModules.naturality_apply (trX n).val g, t.2 n]⟩

/-- Restricting a compatible family of sections along `g` and then along `g'` is restricting it
along `g ≫ g'`. -/
theorem adicSectionsRes_comp {U V W : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (g : U ⟶ V)
    (g' : V ⟶ W) (t : adicSectionsAt B S hS F hF X trX U) :
    adicSectionsRes B S hS F hF X trX g' (adicSectionsRes B S hS F hF X trX g t) =
      adicSectionsRes B S hS F hF X trX (g ≫ g') t :=
  Subtype.ext (funext fun _ => (PresheafOfModules.map_comp_apply _ g g' _).symm)

variable (β : ∀ n : ℕ, X n ⟶ Y n) (hβ : ∀ n : ℕ, trX n ≫ β n = β (n + 1) ≫ trY n)

/-- The map induced by `β` on compatible families of sections commutes with restriction along a
morphism of charts. -/
theorem adicSectionsMapAt_adicSectionsRes {U V : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ}
    (g : U ⟶ V) (t : adicSectionsAt B S hS F hF X trX U) :
    adicSectionsMapAt B S hS F hF X Y trX trY β hβ V (adicSectionsRes B S hS F hF X trX g t) =
      adicSectionsRes B S hS F hF Y trY g (adicSectionsMapAt B S hS F hF X Y trX trY β hβ U t) :=
  Subtype.ext (funext fun n => PresheafOfModules.naturality_apply (β n).val g (t.1 n))

private theorem isSheaf_forget_modules (M : Modules.{u, m} B S hS F hF) :
    Presieve.IsSheaf (SmallEtale.topology B S hS F)
      (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    (GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf)

/-- Two sections of an `𝒪_F`-module over a chart which agree on every affine chart over it are
equal. -/
private theorem eq_of_forall_isAffine_modules (M : Modules.{u, m} B S hS F hF)
    {U : (smallEtaleRingedSite B S hS F hF).C} {x y : M.val.obj (op U)}
    (h : ∀ (V : (smallEtaleRingedSite B S hS F hF).C) (g : V ⟶ U), IsAffine (chartScheme V) →
      M.val.map g.op x = M.val.map g.op y) : x = y :=
  SmallEtale.C1573.eq_of_forall_isAffine B S hS F hF (isSheaf_forget_modules B S hS F hF M) h

/-- **The reduction of `h0882` to affine charts.**  A morphism of inverse systems of
`𝒪_F`-modules which is bijective on the inverse limits of the sections over every affine étale
chart is bijective on the inverse limits of the sections over every étale chart. -/
theorem bijective_adicSectionsMapAt_of_bijective_affineCharts
    (h : ∀ V : (smallEtaleRingedSite B S hS F hF).C, IsAffine (chartScheme V) →
      Function.Bijective (adicSectionsMapAt B S hS F hF X Y trX trY β hβ (op V)))
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) :
    Function.Bijective (adicSectionsMapAt B S hS F hF X Y trX trY β hβ U) := by
  obtain ⟨U⟩ := U
  have hres : ∀ {t t' : adicSectionsAt B S hS F hF X trX (op U)},
      (∀ (V : (smallEtaleRingedSite B S hS F hF).C) (g : V ⟶ U), IsAffine (chartScheme V) →
        adicSectionsRes B S hS F hF X trX g.op t = adicSectionsRes B S hS F hF X trX g.op t') →
      t = t' := by
    intro t t' htt
    refine Subtype.ext (funext fun n => ?_)
    refine eq_of_forall_isAffine_modules B S hS F hF (X n) fun V g hV => ?_
    exact congrArg (fun z : adicSectionsAt B S hS F hF X trX (op V) => z.1 n) (htt V g hV)
  refine ⟨fun t t' htt => hres fun V g hV => (h V hV).1 ?_, fun s => ?_⟩
  · rw [adicSectionsMapAt_adicSectionsRes, adicSectionsMapAt_adicSectionsRes, htt]
  · let e : ∀ V : (smallEtaleRingedSite B S hS F hF).C, IsAffine (chartScheme V) →
        adicSectionsAt B S hS F hF X trX (op V) ≃ adicSectionsAt B S hS F hF Y trY (op V) :=
      fun V hV => Equiv.ofBijective _ (h V hV)
    let tV : ∀ (V : (smallEtaleRingedSite B S hS F hF).C) (_ : V ⟶ U),
        IsAffine (chartScheme V) → adicSectionsAt B S hS F hF X trX (op V) :=
      fun V g hV => (e V hV).symm (adicSectionsRes B S hS F hF Y trY g.op s)
    have htV : ∀ (V : (smallEtaleRingedSite B S hS F hF).C) (g : V ⟶ U)
        (hV : IsAffine (chartScheme V)),
        adicSectionsMapAt B S hS F hF X Y trX trY β hβ (op V) (tV V g hV) =
          adicSectionsRes B S hS F hF Y trY g.op s := fun V g hV => (e V hV).apply_symm_apply _
    have hcompat : ∀ (V₁ V₂ : (smallEtaleRingedSite B S hS F hF).C) (g₁ : V₁ ⟶ U)
        (g₂ : V₂ ⟶ U) (h₁ : IsAffine (chartScheme V₁)) (h₂ : IsAffine (chartScheme V₂))
        (W : (smallEtaleRingedSite B S hS F hF).C) (_ : IsAffine (chartScheme W))
        (a₁ : W ⟶ V₁) (a₂ : W ⟶ V₂), a₁ ≫ g₁ = a₂ ≫ g₂ →
          adicSectionsRes B S hS F hF X trX a₁.op (tV V₁ g₁ h₁) =
            adicSectionsRes B S hS F hF X trX a₂.op (tV V₂ g₂ h₂) := by
      intro V₁ V₂ g₁ g₂ h₁ h₂ W hW a₁ a₂ ha
      refine (h W hW).1 ?_
      rw [adicSectionsMapAt_adicSectionsRes, adicSectionsMapAt_adicSectionsRes, htV V₁ g₁ h₁,
        htV V₂ g₂ h₂, adicSectionsRes_comp, adicSectionsRes_comp, ← op_comp, ← op_comp, ha]
    have hglue : ∀ n : ℕ, ∃ x : (X n).val.obj (op U),
        ∀ (V : (smallEtaleRingedSite B S hS F hF).C) (g : V ⟶ U)
          (hV : IsAffine (chartScheme V)), (X n).val.map g.op x = (tV V g hV).1 n := fun n =>
      SmallEtale.C1573.exists_eq_of_forall_isAffine B S hS F hF
        (isSheaf_forget_modules B S hS F hF (X n)) (fun V g hV => (tV V g hV).1 n)
        fun V₁ V₂ g₁ g₂ h₁ h₂ W hW a₁ a₂ ha =>
          congrArg (fun z : adicSectionsAt B S hS F hF X trX (op W) => z.1 n)
            (hcompat V₁ V₂ g₁ g₂ h₁ h₂ W hW a₁ a₂ ha)
    choose x hx using hglue
    refine ⟨⟨x, fun n => ?_⟩, ?_⟩
    · refine eq_of_forall_isAffine_modules B S hS F hF (X n) fun V g hV => ?_
      refine (PresheafOfModules.naturality_apply (trX n).val g.op (x (n + 1))).symm.trans ?_
      exact (congrArg _ (hx (n + 1) V g hV)).trans (((tV V g hV).2 n).trans (hx n V g hV).symm)
    · refine Subtype.ext (funext fun n => ?_)
      refine eq_of_forall_isAffine_modules B S hS F hF (Y n) fun V g hV => ?_
      refine (PresheafOfModules.naturality_apply (β n).val g.op (x n)).symm.trans ?_
      exact (congrArg _ (hx n V g hV)).trans
        (congrArg (fun z : adicSectionsAt B S hS F hF Y trY (op V) => z.1 n) (htV V g hV))

end Sections

end AlgebraicGeometry.Space.C1573

end
