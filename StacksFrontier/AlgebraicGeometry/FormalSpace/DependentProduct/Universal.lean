module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange

/-!
# The universal property of the dependent product of fppf sheaves

Let `i : I ⟶ X` and `p : W ⟶ I` be morphisms of fppf sheaves on the big fppf site of a scheme
`S`, with dependent product `Π_i W`
(`AlgebraicGeometry.FormalSpace.DependentProduct.liftAlong`). A morphism `ζ : Z ⟶ X` together
with an identification of `Z ×_X I` with `W` over `I` induces a morphism `Z ⟶ Π_i W` over `X`,
and a morphism `Z ⟶ Π_i W` over `X` is determined by the morphism `Z ×_X I ⟶ W` it induces.
These are the two halves of the universal property of the dependent product used to identify
it with a representable sheaf.

## Main definitions

* `AlgebraicGeometry.FormalSpace.DependentProduct.liftAlongMk`: the morphism `Z ⟶ Π_i W` over
  `X` attached to a square cartesian on sections.

## Main results

* `AlgebraicGeometry.FormalSpace.DependentProduct.liftAlongMk_comp_liftAlongBase` and
  `AlgebraicGeometry.FormalSpace.DependentProduct.comp_liftAlongMk`: the two identities it
  satisfies.
* `AlgebraicGeometry.FormalSpace.DependentProduct.liftAlong_hom_ext`: a morphism into `Π_i W`
  over `X` is determined by its lifting rule at the identity.

## References

* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms into the dependent product -/

section Mk

variable {B S hS} {X I W Z : FppfSheaf B S hS} {i : I ⟶ X} {p : W ⟶ I} {ζ : Z ⟶ X}
  {c₀ : W ⟶ Z} (hex : IsSectionwisePullback B S hS c₀ p ζ i)

/-- The lifting rule of the section of `Π_i W` attached to a section of `Z`: the unique
section of `W` above the restricted section of `Z` and the given section of `I`. -/
def mkRule {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (ζ.hom.app (Opposite.op T) z)) :
    W.obj.obj (Opposite.op T') :=
  bcPoint hex (Z.obj.map s.op z) w ((app_map_op B S hS ζ s z).trans h.symm)

/-- The section `mkRule hex z T' s w h` of `W` maps to the restriction of `z` along `s` in `Z`. -/
theorem mkRule_fst {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (ζ.hom.app (Opposite.op T) z)) :
    c₀.hom.app (Opposite.op T') (mkRule hex z T' s w h) = Z.obj.map s.op z :=
  bcPoint_fst hex _ _ _

/-- The section `mkRule hex z T' s w h` of `W` maps to `w` in `I`. -/
theorem mkRule_snd {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (ζ.hom.app (Opposite.op T) z)) :
    p.hom.app (Opposite.op T') (mkRule hex z T' s w h) = w :=
  bcPoint_snd hex _ _ _

/-- Restricting `mkRule hex z T' s w h` along `r : T'' ⟶ T'` gives the section attached to
`r ≫ s` and the restriction of `w`. -/
theorem mkRule_map {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (T' T'' : BigFppfOver B S hS) (r : T'' ⟶ T') (s : T' ⟶ T)
    (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (ζ.hom.app (Opposite.op T) z))
    (h' : i.hom.app (Opposite.op T'') (I.obj.map r.op w)
      = X.obj.map (r ≫ s).op (ζ.hom.app (Opposite.op T) z)) :
    W.obj.map r.op (mkRule hex z T' s w h)
      = mkRule hex z T'' (r ≫ s) (I.obj.map r.op w) h' := by
  refine bcPoint_eq hex _ _ _ _ ?_ ?_
  · exact (app_map_op B S hS c₀ r (mkRule hex z T' s w h)).trans
      ((congrArg (Z.obj.map r.op) (mkRule_fst hex z T' s w h)).trans
        (LiftAlong.map_comp_op_apply Z.obj s r z).symm)
  · exact (app_map_op B S hS p r (mkRule hex z T' s w h)).trans
      (congrArg (I.obj.map r.op) (mkRule_snd hex z T' s w h))

/-- The section of `Π_i W` attached to a section of `Z`. -/
def mkApp (T : BigFppfOver B S hS) (z : Z.obj.obj (Opposite.op T)) :
    LiftAlong B S hS i p T where
  base := ζ.hom.app (Opposite.op T) z
  lift := mkRule hex z
  lift_proj := fun T' s w h ↦ mkRule_snd hex z T' s w h
  lift_map := fun T' T'' r s w h h' ↦ mkRule_map hex z T' T'' r s w h h'

/-- Restricting the section `mkApp hex T z` of `Π_i W` along `r : T₀ ⟶ T` gives the section
attached to the restriction of `z` along `r`. -/
theorem mkApp_restrict {T T₀ : BigFppfOver B S hS} (r : T₀ ⟶ T)
    (z : Z.obj.obj (Opposite.op T)) :
    (mkApp hex T z).restrict r = mkApp hex T₀ (Z.obj.map r.op z) := by
  refine LiftAlong.ext _ _ (app_map_op B S hS ζ r z).symm fun T' t w h h' ↦ ?_
  have hb : i.hom.app (Opposite.op T') w
      = X.obj.map (t ≫ r).op (ζ.hom.app (Opposite.op T) z) :=
    h.trans (LiftAlong.map_comp_op_apply X.obj r t (ζ.hom.app (Opposite.op T) z)).symm
  have hL : i.hom.app (Opposite.op T') w
      = X.obj.map t.op (ζ.hom.app (Opposite.op T₀) (Z.obj.map r.op z)) := h'
  refine Eq.trans (LiftAlong.restrict_lift r (mkApp hex T z) rfl h hb) ?_
  refine bcPoint_eq hex (Z.obj.map t.op (Z.obj.map r.op z)) w
    ((app_map_op B S hS ζ t (Z.obj.map r.op z)).trans hL.symm) _ ?_ ?_
  · exact (mkRule_fst hex z T' (t ≫ r) w hb).trans
      (LiftAlong.map_comp_op_apply Z.obj r t z)
  · exact mkRule_snd hex z T' (t ≫ r) w hb

/-- **The morphism `Z ⟶ Π_i W` over `X` attached to an identification of `Z ×_X I` with `W`
over `I`.** This is the half of the universal property of the dependent product which produces
morphisms into it. -/
def liftAlongMk : Z ⟶ liftAlong B S hS i p :=
  ⟨{ app := fun T ↦ TypeCat.ofHom (mkApp hex T.unop)
     naturality := fun _ _ r ↦ ConcreteCategory.hom_ext _ _ fun z ↦
       (mkApp_restrict hex r.unop z).symm }⟩

/-- The value of `liftAlongMk hex` on a section `z` of `Z` over `T` is `mkApp hex T z`. -/
@[simp]
theorem liftAlongMk_app_apply (T : BigFppfOver B S hS) (z : Z.obj.obj (Opposite.op T)) :
    (liftAlongMk hex).hom.app (Opposite.op T) z = mkApp hex T z :=
  rfl

/-- The morphism `liftAlongMk hex : Z ⟶ Π_i W` lies over `ζ : Z ⟶ X`. -/
theorem liftAlongMk_comp_liftAlongBase :
    liftAlongMk hex ≫ liftAlongBase B S hS i p = ζ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl))

/-- If `i` is injective on sections, then composing `c₀ : W ⟶ Z` with `liftAlongMk hex` gives
the morphism `liftAlongSection B S hS hi : W ⟶ Π_i W`. -/
theorem comp_liftAlongMk (hw : c₀ ≫ ζ = p ≫ i)
    (hi : ∀ T : BigFppfOver B S hS, Function.Injective (i.hom.app (Opposite.op T))) :
    c₀ ≫ liftAlongMk hex = liftAlongSection B S hS hi := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦
    ConcreteCategory.hom_ext _ _ fun y ↦ ?_))
  have hbase : ζ.hom.app T (c₀.hom.app T y) = i.hom.app T (p.hom.app T y) :=
    congrArg (fun k : W ⟶ X ↦ k.hom.app T y) hw
  show mkApp hex T.unop (c₀.hom.app T y) = liftAlongSectionApp B S hS hi p T.unop y
  refine LiftAlong.ext _ _ hbase fun T' t w h h' ↦ ?_
  have hLh : i.hom.app (Opposite.op T') w
      = X.obj.map t.op (ζ.hom.app T (c₀.hom.app T y)) := h
  have hLh' : i.hom.app (Opposite.op T') w
      = X.obj.map t.op (i.hom.app T (p.hom.app T y)) := h'
  have hwt : w = I.obj.map t.op (p.hom.app T y) :=
    hi T' (hLh'.trans (app_map_op B S hS i t (p.hom.app T y)).symm)
  refine (bcPoint_eq hex (Z.obj.map t.op (c₀.hom.app T y)) w
    ((app_map_op B S hS ζ t (c₀.hom.app T y)).trans hLh.symm)
    (W.obj.map t.op y) ?_ ?_).symm
  · exact app_map_op B S hS c₀ t y
  · exact (app_map_op B S hS p t y).trans hwt.symm

end Mk

/-! ### Morphisms into the dependent product are determined on the fibre product -/

section HomExt

variable {B S hS} {X I W Z : FppfSheaf B S hS} {i : I ⟶ X} {p : W ⟶ I}

/-- **A morphism `Z ⟶ Π_i W` over `X` is determined by the morphism `Z ×_X I ⟶ W` it
induces.** The hypothesis is that the two morphisms agree over `X` and that their lifting rules
agree at the identity, which is the value of the induced morphism on `Z ×_X I`; the rule at a
general stage is recovered from the rule at the identity by naturality. -/
theorem liftAlong_hom_ext {e e' : Z ⟶ liftAlong B S hS i p}
    (hbase : e ≫ liftAlongBase B S hS i p = e' ≫ liftAlongBase B S hS i p)
    (hrule : ∀ (T : BigFppfOver B S hS) (z : Z.obj.obj (Opposite.op T))
      (w : I.obj.obj (Opposite.op T))
      (h : i.hom.app (Opposite.op T) w
        = X.obj.map (𝟙 T).op (e.hom.app (Opposite.op T) z).base)
      (h' : i.hom.app (Opposite.op T) w
        = X.obj.map (𝟙 T).op (e'.hom.app (Opposite.op T) z).base),
      (e.hom.app (Opposite.op T) z).lift T (𝟙 T) w h
        = (e'.hom.app (Opposite.op T) z).lift T (𝟙 T) w h') :
    e = e' := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦
    ConcreteCategory.hom_ext _ _ fun z ↦ ?_))
  have hb : (e.hom.app T z).base = (e'.hom.app T z).base :=
    congrArg (fun k : Z ⟶ X ↦ k.hom.app T z) hbase
  refine LiftAlong.ext _ _ hb fun T' s w h h' ↦ ?_
  have key : ∀ (f : Z ⟶ liftAlong B S hS i p)
      (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (f.hom.app T z).base),
      ∃ hA : i.hom.app (Opposite.op T') w
        = X.obj.map (𝟙 T').op (f.hom.app (Opposite.op T') (Z.obj.map s.op z)).base,
      (f.hom.app (Opposite.op T') (Z.obj.map s.op z)).lift T' (𝟙 T') w hA
        = (f.hom.app T z).lift T' s w h := fun f h ↦ by
    have hnat := app_map_op B S hS f s z
    have hA : i.hom.app (Opposite.op T') w
        = X.obj.map (𝟙 T').op (f.hom.app (Opposite.op T') (Z.obj.map s.op z)).base := by
      rw [congrArg LiftAlong.base hnat, op_id, FunctorToTypes.map_id_apply]
      exact h
    exact ⟨hA, LiftAlong.lift_eq_of_eq_restrict _ s _ hnat (Category.id_comp s) rfl hA h⟩
  obtain ⟨hA, e₁⟩ := key e h
  obtain ⟨hA', e₂⟩ := key e' h'
  exact e₁.symm.trans ((hrule T' (Z.obj.map s.op z) w hA hA').trans e₂)

end HomExt

end AlgebraicGeometry.FormalSpace.DependentProduct

end
