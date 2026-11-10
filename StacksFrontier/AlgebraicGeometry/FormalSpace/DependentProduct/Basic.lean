module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dependent product of fppf sheaves along a morphism

Let `S` be a scheme contained in a big fppf site `B`, and let `i : I ⟶ X` and `p : W ⟶ I` be
morphisms of fppf sheaves on the big fppf site of `S`. The *dependent product* `Π_i W` of `p`
along `i` is the fppf sheaf whose sections over an object `T` of the site are the pairs `(a, b)`
with `a : T ⟶ X` and `b : T ×_{a, X} I ⟶ W` a morphism over `I`. It is the right adjoint of base
change along `i`, evaluated at `p`.

When `i` is injective on sections, base change of the dependent product along `i` gives back
`W`: the square formed by `W ⟶ Π_i W`, `p`, the structure morphism `Π_i W ⟶ X` and `i` is
cartesian. This is the device by which an étale object over a thickening `I` of `X` is
transported to an object over `X`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.DependentProduct.LiftAlong`: a section of `Π_i W` over an
  object of the site, as a structure.
* `AlgebraicGeometry.FormalSpace.DependentProduct.liftAlong`: the fppf sheaf `Π_i W`, and
  `AlgebraicGeometry.FormalSpace.DependentProduct.liftAlongBase` its structure morphism to `X`.
* `AlgebraicGeometry.FormalSpace.DependentProduct.liftAlongSection`: the comparison
  `W ⟶ Π_i W`, when `i` is injective on sections.
* `AlgebraicGeometry.FormalSpace.DependentProduct.liftAlongMap`: functoriality in `W`.

## Main results

* `AlgebraicGeometry.FormalSpace.DependentProduct.isSheaf_liftAlongPresheaf`: `Π_i W` is a sheaf
  for the fppf topology.
* `AlgebraicGeometry.FormalSpace.DependentProduct.isPullback_liftAlongSection`: `W` is the fibre
  product `Π_i W ×_X I` when `i` is injective on sections.
* `AlgebraicGeometry.FormalSpace.DependentProduct.isIso_liftAlongBase_id`: the dependent product
  of the identity of `I` is `X`.

## Implementation notes

A section of `Π_i W` over `T` is recorded as a structure rather than as a morphism out of a
fibre product of presheaves, because the fibre product `T ×_{a, X} I` depends on `a` and would
have to be chosen. The rule `b` is therefore a dependent function whose domain mentions the
section `a`; comparing the rules of two sections uses the congruence lemma
`AlgebraicGeometry.FormalSpace.DependentProduct.LiftAlong.lift_congr`.

The construction and its proofs follow the quasi-inverse functor of the proof of Stacks 0DEG,
where the same dependent product appears along the inclusion of a reduction; here it is stated
for an arbitrary morphism `i`.

## References

* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X I W : FppfSheaf B S hS}

/-- A section of the sheaf `Π_i W` over an object `T` of the big fppf site. -/
@[sga "3 I 6.4" "special case"]
structure LiftAlong (i : I ⟶ X) (p : W ⟶ I) (T : BigFppfOver B S hS) where
  /-- The morphism `a : T ⟶ X`. -/
  base : X.obj.obj (Opposite.op T)
  /-- The morphism `b : T ×_{a, X} I ⟶ W`, as a rule on points. -/
  lift : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T) (w : I.obj.obj (Opposite.op T')),
    i.hom.app (Opposite.op T') w = X.obj.map t.op base → W.obj.obj (Opposite.op T')
  /-- The condition `p ∘ b = a` restricted to the fibre product. -/
  lift_proj : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map t.op base),
    p.hom.app (Opposite.op T') (lift T' t w h) = w
  /-- `b` is a morphism of presheaves. -/
  lift_map : ∀ (T' T'' : BigFppfOver B S hS) (s : T'' ⟶ T') (t : T' ⟶ T)
    (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map t.op base)
    (h' : i.hom.app (Opposite.op T'') (I.obj.map s.op w) = X.obj.map (s ≫ t).op base),
    W.obj.map s.op (lift T' t w h) = lift T'' (s ≫ t) (I.obj.map s.op w) h'

namespace LiftAlong

variable {B S hS} {i : I ⟶ X} {p : W ⟶ I} {T : BigFppfOver B S hS}

/-- Restriction along a composite, on a presheaf of the big fppf site. -/
theorem map_comp_op_apply (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    {A A' A'' : BigFppfOver B S hS} (t : A' ⟶ A) (s : A'' ⟶ A') (x : F.obj (Opposite.op A)) :
    F.map (s ≫ t).op x = F.map s.op (F.map t.op x) := by
  rw [op_comp, Functor.map_comp_apply]

/-- The lifting rule of a section of `Π_i W` depends on its morphism argument only through
that morphism, the compatibility proof being irrelevant. -/
theorem lift_congr {ξ η : LiftAlong B S hS i p T} (hξ : ξ = η) {T' : BigFppfOver B S hS}
    {t t' : T' ⟶ T} (ht : t = t') {w w' : I.obj.obj (Opposite.op T')} (hw : w = w')
    (h : i.hom.app (Opposite.op T') w = X.obj.map t.op ξ.base)
    (h' : i.hom.app (Opposite.op T') w' = X.obj.map t'.op η.base) :
    ξ.lift T' t w h = η.lift T' t' w' h' := by
  subst hξ; subst ht; subst hw; rfl

/-- Two sections of `Π_i W` agree as soon as their bases and their lifting rules do. -/
theorem ext : ∀ (ξ η : LiftAlong B S hS i p T), ξ.base = η.base →
    (∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
      (h : i.hom.app (Opposite.op T') w = X.obj.map t.op ξ.base)
      (h' : i.hom.app (Opposite.op T') w = X.obj.map t.op η.base),
      ξ.lift T' t w h = η.lift T' t w h') → ξ = η := by
  rintro ⟨b, l, hp, hm⟩ ⟨b', l', hp', hm'⟩ hbase hlift
  subst hbase
  simp only [mk.injEq, heq_eq_eq, true_and]
  exact funext fun T' ↦ funext fun t ↦ funext fun w ↦ funext fun h ↦ hlift T' t w h h

/-- Restriction of a section of `Π_i W` along a morphism of the site. -/
def restrict {T₀ : BigFppfOver B S hS} (r : T₀ ⟶ T) (ξ : LiftAlong B S hS i p T) :
    LiftAlong B S hS i p T₀ where
  base := X.obj.map r.op ξ.base
  lift T' t w h := ξ.lift T' (t ≫ r) w (by rw [h, map_comp_op_apply])
  lift_proj T' t w h := ξ.lift_proj T' (t ≫ r) w _
  lift_map T' T'' s t w h h' :=
    (ξ.lift_map T' T'' s (t ≫ r) w _
      (by rw [h']; simp only [map_comp_op_apply])).trans
      (lift_congr rfl (Category.assoc s t r).symm rfl _ _)

/-- The base of a restricted section is the restriction of the base. -/
@[simp]
theorem restrict_base {T₀ : BigFppfOver B S hS} (r : T₀ ⟶ T) (ξ : LiftAlong B S hS i p T) :
    (ξ.restrict r).base = X.obj.map r.op ξ.base :=
  rfl

/-- The lifting rule of a restricted section is the lifting rule of the original section along
the composite morphism. -/
theorem restrict_lift {T₀ : BigFppfOver B S hS} (r : T₀ ⟶ T) (ξ : LiftAlong B S hS i p T)
    {T' : BigFppfOver B S hS} {t : T' ⟶ T₀} {t' : T' ⟶ T} (ht : t ≫ r = t')
    {w : I.obj.obj (Opposite.op T')}
    (h : i.hom.app (Opposite.op T') w = X.obj.map t.op (ξ.restrict r).base)
    (h' : i.hom.app (Opposite.op T') w = X.obj.map t'.op ξ.base) :
    (ξ.restrict r).lift T' t w h = ξ.lift T' t' w h' := by
  subst ht; rfl

/-- Restriction along the identity is the identity. -/
theorem restrict_id (ξ : LiftAlong B S hS i p T) : ξ.restrict (𝟙 T) = ξ := by
  refine ext _ _ (by simp) fun T' t w h h' ↦ ?_
  exact restrict_lift _ ξ (Category.comp_id t) h h'

/-- Restricting along `r` and then along `r'` is restriction along `r' ≫ r`. -/
theorem restrict_restrict {T₁ T₂ : BigFppfOver B S hS} (r : T₁ ⟶ T) (r' : T₂ ⟶ T₁)
    (ξ : LiftAlong B S hS i p T) :
    (ξ.restrict r).restrict r' = ξ.restrict (r' ≫ r) := by
  refine ext _ _ (by simp) fun T₃ t w h h' ↦ ?_
  have h₂ : i.hom.app (Opposite.op T₃) w = X.obj.map (t ≫ r').op (ξ.restrict r).base := by
    rw [h]; simp
  have H : i.hom.app (Opposite.op T₃) w = X.obj.map ((t ≫ r') ≫ r).op ξ.base := by
    rw [h₂]; simp
  have H' : i.hom.app (Opposite.op T₃) w = X.obj.map (t ≫ r' ≫ r).op ξ.base := by
    rw [H]; simp
  rw [restrict_lift r' (ξ.restrict r) rfl h h₂, restrict_lift r ξ rfl h₂ H,
    lift_congr rfl (Category.assoc t r' r) rfl H H',
    ← restrict_lift (r' ≫ r) ξ rfl h' H']

/-- Comparison of the lifting rules of a section and of its restriction, across the two
objects of the site. -/
theorem lift_eq_of_eq_restrict {Y Z : BigFppfOver B S hS} (ξ : LiftAlong B S hS i p Y)
    (g : Z ⟶ Y) (η : LiftAlong B S hS i p Z) (hη : η = ξ.restrict g)
    {Z' : BigFppfOver B S hS} {t : Z' ⟶ Z} {t' : Z' ⟶ Y} (ht : t ≫ g = t')
    {w w' : I.obj.obj (Opposite.op Z')} (hw : w = w')
    (h : i.hom.app (Opposite.op Z') w = X.obj.map t.op η.base)
    (h' : i.hom.app (Opposite.op Z') w' = X.obj.map t'.op ξ.base) :
    η.lift Z' t w h = ξ.lift Z' t' w' h' := by
  subst hη; subst hw
  exact restrict_lift g ξ ht h h'

end LiftAlong

/-- The presheaf `Π_i W`: a section over `T` is a morphism
`a : T ⟶ X` together with a morphism `b : T ×_{a, X} I ⟶ W` over `I`. -/
def liftAlongPresheaf (i : I ⟶ X) (p : W ⟶ I) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj T := LiftAlong B S hS i p T.unop
  map r := TypeCat.ofHom fun ξ ↦ ξ.restrict r.unop
  map_id _T := ConcreteCategory.hom_ext _ _ fun ξ ↦ ξ.restrict_id
  map_comp r r' := ConcreteCategory.hom_ext _ _ fun ξ ↦
    (LiftAlong.restrict_restrict r.unop r'.unop ξ).symm

/-- The presheaf `Π_i W` acts on morphisms by restriction of sections. -/
@[simp]
theorem liftAlongPresheaf_map_apply (i : I ⟶ X) (p : W ⟶ I) {T T' : BigFppfOver B S hS}
    (g : T' ⟶ T) (ξ : LiftAlong B S hS i p T) :
    (liftAlongPresheaf B S hS i p).map g.op ξ = ξ.restrict g :=
  rfl

/-! ### `Π_i W` is a sheaf for the fppf topology -/

/-- Naturality of a morphism of fppf sheaves, read on sections. -/
theorem app_map_op {Y Z : FppfSheaf B S hS} (f : Y ⟶ Z) {A A' : BigFppfOver B S hS}
    (s : A' ⟶ A) (w : Y.obj.obj (Opposite.op A)) :
    f.hom.app (Opposite.op A') (Y.obj.map s.op w)
      = Z.obj.map s.op (f.hom.app (Opposite.op A) w) :=
  NatTrans.naturality_apply f.hom s.op w

/-- Two morphisms of fppf sheaves are equal if they agree on all sections. -/
private theorem hom_ext_apply {Y Z : FppfSheaf B S hS} {f g : Y ⟶ Z}
    (h : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (y : Y.obj.obj T), f.hom.app T y = g.hom.app T y) :
    f = g :=
  Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ (h T)))

variable {i : I ⟶ X} {p : W ⟶ I}

/-- The presheaf `Π_i W` is a sheaf for the fppf topology: the morphism
`a : T ⟶ X` glues because `X` is a sheaf, and the morphism `b` glues because `W` is a sheaf and
the fppf topology is stable under base change, so a covering sieve of `T` pulls back to a
covering sieve of every object mapping to `T`. -/
theorem isSheaf_liftAlongPresheaf (i : I ⟶ X) (p : W ⟶ I) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (liftAlongPresheaf B S hS i p) := by
  rw [isSheaf_iff_isSheaf_of_type]
  have hX := (isSheaf_iff_isSheaf_of_type _ _).mp X.property
  have hI := (isSheaf_iff_isSheaf_of_type _ _).mp I.property
  have hW := (isSheaf_iff_isSheaf_of_type _ _).mp W.property
  intro T R hR x hx
  -- the family depends on its arrow only through that arrow
  have hxc : ∀ {Y : BigFppfOver B S hS} {f f' : Y ⟶ T} (_ : f = f')
      (hf : R.arrows f) (hf' : R.arrows f'), x f hf = x f' hf' := by
    intro Y f f' hff hf hf'
    subst hff; rfl
  -- restricting a member of the family along an arrow gives another member
  have hxs : ∀ {Y Z : BigFppfOver B S hS} (f : Y ⟶ T) (g : Z ⟶ Y) (hf : R.arrows f)
      (hgf : R.arrows (g ≫ f)), (x f hf).restrict g = x (g ≫ f) hgf := fun f g hf hgf ↦
    ((Presieve.compatible_iff_sieveCompatible x).mp hx f g hf).symm
  -- Step A: the morphism `a : T ⟶ X`, glued from the bases of the family.
  obtain ⟨a, ha, hau⟩ := hX R hR (fun _ f hf ↦ (x f hf).base)
    ((Presieve.compatible_iff_sieveCompatible _).mpr fun {_ _} f g hf ↦
      (congrArg LiftAlong.base (hxs f g hf (R.downward_closed hf g))).symm)
  have ha' : ∀ {Y : BigFppfOver B S hS} (f : Y ⟶ T) (hf : R.arrows f),
      X.obj.map f.op a = (x f hf).base := fun f hf ↦ ha f hf
  -- the compatibility proof the family of lifts needs at each stage
  have hfib : ∀ {T' T'' : BigFppfOver B S hS} (t : T' ⟶ T) (s : T'' ⟶ T')
      (hs : R.arrows (s ≫ t)) (w : I.obj.obj (Opposite.op T'))
      (_ : i.hom.app (Opposite.op T') w = X.obj.map t.op a),
      i.hom.app (Opposite.op T'') (I.obj.map s.op w)
        = X.obj.map (𝟙 T'').op (x (s ≫ t) hs).base := by
    intro T' T'' t s hs w h
    rw [app_map_op, h, ← ha' (s ≫ t) hs]
    simp
  -- Step B: the morphism `b`, glued from the lifts of the family.
  have hgl : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
      (h : i.hom.app (Opposite.op T') w = X.obj.map t.op a),
      ∃! c : W.obj.obj (Opposite.op T'),
        ∀ (T'' : BigFppfOver B S hS) (s : T'' ⟶ T') (hs : R.arrows (s ≫ t)),
          W.obj.map s.op c
            = (x (s ≫ t) hs).lift T'' (𝟙 T'') (I.obj.map s.op w) (hfib t s hs w h) := by
    intro T' t w h
    have hRt : R.pullback t ∈ BigFppfOver.topology B S hS T' :=
      (BigFppfOver.topology B S hS).pullback_stable t hR
    obtain ⟨c, hc, hcu⟩ := hW (R.pullback t) hRt
      (fun T'' s hs ↦ (x (s ≫ t) hs).lift T'' (𝟙 T'') (I.obj.map s.op w) (hfib t s hs w h))
      ((Presieve.compatible_iff_sieveCompatible _).mpr fun {Y Z} s g hs ↦
        (LiftAlong.lift_eq_of_eq_restrict (x (s ≫ t) hs) g _
            ((hxc (Category.assoc g s t) _ (R.downward_closed hs g)).trans
              (hxs (s ≫ t) g hs (R.downward_closed hs g)).symm)
            (by simp) (LiftAlong.map_comp_op_apply I.obj s g w) _ _).trans
          ((x (s ≫ t) hs).lift_map Y Z g (𝟙 Y) (I.obj.map s.op w) (hfib t s hs w h)
            (by rw [app_map_op, hfib t s hs w h, LiftAlong.map_comp_op_apply])).symm)
    exact ⟨c, fun T'' s hs ↦ hc s hs, fun c' hc' ↦ hcu c' fun {T''} s hs ↦ hc' T'' s hs⟩
  refine ⟨⟨a, fun T' t w h ↦ (hgl T' t w h).choose, ?_, ?_⟩, ?_, ?_⟩
  · -- `p ∘ b = a` on the fibre product: both sides glue the same family on `I`.
    intro T' t w h
    have hRt : R.pullback t ∈ BigFppfOver.topology B S hS T' :=
      (BigFppfOver.topology B S hS).pullback_stable t hR
    refine (hI (R.pullback t) hRt).isSeparatedFor
      (fun (T'' : BigFppfOver B S hS) (s : T'' ⟶ T') _ ↦ I.obj.map s.op w) _ _
      (fun {T''} s hs ↦ ?_) (fun {T''} s _ ↦ rfl)
    rw [← app_map_op B S hS p s, (hgl T' t w h).choose_spec.1 T'' s hs]
    exact (x (s ≫ t) hs).lift_proj T'' (𝟙 T'') (I.obj.map s.op w) _
  · -- `b` is a morphism of presheaves
    intro T' T'' s t w h h'
    refine (hgl T'' (s ≫ t) (I.obj.map s.op w) h').choose_spec.2 _ fun Z r hr ↦ ?_
    rw [← LiftAlong.map_comp_op_apply,
      (hgl T' t w h).choose_spec.1 Z (r ≫ s) (by rwa [Category.assoc])]
    exact LiftAlong.lift_congr (hxc (Category.assoc r s t) _ hr) rfl
      (LiftAlong.map_comp_op_apply I.obj s r w) _ _
  · -- the glued section restricts to the given family
    intro Y f hf
    refine LiftAlong.ext _ _ (ha' f hf) fun T' t w h h' ↦ ?_
    have H : i.hom.app (Opposite.op T') w = X.obj.map (t ≫ f).op a := by
      rw [h]; simp
    refine (LiftAlong.restrict_lift f _ rfl h H).trans ?_
    refine ((hgl T' (t ≫ f) w H).choose_spec.2 ((x f hf).lift T' t w h')
      fun T'' s hs ↦ ?_).symm
    refine ((x f hf).lift_map T' T'' s t w h'
      (by rw [app_map_op, h']; simp)).trans ?_
    have hgf : R.arrows ((s ≫ t) ≫ f) := by rwa [Category.assoc]
    exact (LiftAlong.lift_eq_of_eq_restrict (x f hf) (s ≫ t) _
      ((hxc (Category.assoc s t f) hgf hs).symm.trans
        (hxs f (s ≫ t) hf hgf).symm)
      (by simp) rfl _ _).symm
  · -- uniqueness
    intro ζ hζ
    have hζ' : ∀ {Y : BigFppfOver B S hS} (f : Y ⟶ T) (hf : R.arrows f),
        ζ.restrict f = x f hf := fun f hf ↦ hζ f hf
    refine LiftAlong.ext _ _ (hau _ fun {Y} f hf ↦ congrArg LiftAlong.base (hζ f hf))
      fun T' t w h h' ↦ ?_
    refine (hgl T' t w h').choose_spec.2 _ fun T'' s hs ↦ ?_
    refine (ζ.lift_map T' T'' s t w h
      (by rw [app_map_op, h]; simp)).trans ?_
    exact (LiftAlong.lift_eq_of_eq_restrict ζ (s ≫ t) _ (hζ' (s ≫ t) hs).symm
      (by simp) rfl _ _).symm


/-! ### `Π_i W` as an fppf sheaf over `X` -/

section Construction

variable (i : I ⟶ X) (p : W ⟶ I)

/-- Composition of morphisms of fppf sheaves, read on sections. -/
theorem comp_app_apply {A C D : FppfSheaf B S hS} (f : A ⟶ C) (g : C ⟶ D)
    (T : BigFppfOver B S hS) (z : A.obj.obj (Opposite.op T)) :
    (f ≫ g).hom.app (Opposite.op T) z
      = g.hom.app (Opposite.op T) (f.hom.app (Opposite.op T) z) :=
  rfl

/-- The dependent product `Π_i W`: the fppf sheaf whose sections
over `T` are the pairs `(a, b)` with `a : T ⟶ X` and `b : T ×_{a, X} I ⟶ W` over `I`. -/
@[sga "3 I 6.4" "special case"]
def liftAlong (i : I ⟶ X) (p : W ⟶ I) : FppfSheaf B S hS :=
  ⟨liftAlongPresheaf B S hS i p, isSheaf_liftAlongPresheaf B S hS i p⟩

/-- The structure morphism `Π_i W ⟶ X`, `(a, b) ↦ a`. -/
def liftAlongBase (i : I ⟶ X) (p : W ⟶ I) : liftAlong B S hS i p ⟶ X :=
  ⟨{ app := fun _ ↦ TypeCat.ofHom LiftAlong.base
     naturality := fun _ _ _ ↦ ConcreteCategory.hom_ext _ _ fun _ ↦ rfl }⟩

/-- The structure morphism `Π_i W ⟶ X` sends a section `(a, b)` to `a`. -/
@[simp]
theorem liftAlongBase_app_apply (i : I ⟶ X) (p : W ⟶ I) (T : BigFppfOver B S hS)
    (ξ : LiftAlong B S hS i p T) :
    (liftAlongBase B S hS i p).hom.app (Opposite.op T) ξ = ξ.base :=
  rfl

variable {i p} (hi : ∀ T : BigFppfOver B S hS, Function.Injective (i.hom.app (Opposite.op T)))

/-- The section of `Π_i W` over `T` attached to a section of `W`: its morphism to `X` is
`i ∘ p`, and its morphism from the fibre product `T ×_X I` — which is `T` itself, `i` being
injective on sections — is the given section. -/
def liftAlongSectionApp (p : W ⟶ I) (T : BigFppfOver B S hS)
    (y : W.obj.obj (Opposite.op T)) : LiftAlong B S hS i p T where
  base := i.hom.app (Opposite.op T) (p.hom.app (Opposite.op T) y)
  lift _T' t _ _ := W.obj.map t.op y
  lift_proj T' t _w h :=
    (app_map_op B S hS p t y).trans
      (hi T' ((app_map_op B S hS i t (p.hom.app (Opposite.op T) y)).trans h.symm))
  lift_map _T' _T'' s t _w _h _h' := (LiftAlong.map_comp_op_apply W.obj t s y).symm

/-- The section of `Π_i W` attached to a section `y` of `W`, restricted along `r`, is the
section attached to the restriction of `y` along `r`. -/
theorem liftAlongSectionApp_restrict (T T' : BigFppfOver B S hS) (r : T' ⟶ T)
    (y : W.obj.obj (Opposite.op T)) :
    (liftAlongSectionApp B S hS hi p T y).restrict r
      = liftAlongSectionApp B S hS hi p T' (W.obj.map r.op y) :=
  LiftAlong.ext _ _
    (((congrArg (i.hom.app (Opposite.op T')) (app_map_op B S hS p r y)).trans
      (app_map_op B S hS i r (p.hom.app (Opposite.op T) y))).symm)
    fun _T'' t _w _ _ ↦ LiftAlong.map_comp_op_apply W.obj r t y

/-- The comparison `W ⟶ Π_i W`. -/
def liftAlongSection : W ⟶ liftAlong B S hS i p :=
  ⟨{ app := fun T ↦ TypeCat.ofHom (liftAlongSectionApp B S hS hi p T.unop)
     naturality := fun T T' r ↦ ConcreteCategory.hom_ext _ _ fun y ↦
       (liftAlongSectionApp_restrict B S hS hi T.unop T'.unop r.unop y).symm }⟩

/-- The comparison `W ⟶ Π_i W` sends a section `y` of `W` to `liftAlongSectionApp` of `y`. -/
@[simp]
theorem liftAlongSection_app_apply (T : BigFppfOver B S hS)
    (y : W.obj.obj (Opposite.op T)) :
    (liftAlongSection B S hS hi).hom.app (Opposite.op T) y
      = liftAlongSectionApp B S hS hi p T y :=
  rfl

/-- The composite of the comparison `W ⟶ Π_i W` with the structure morphism `Π_i W ⟶ X` is
`p ≫ i`. -/
theorem liftAlongSection_comp_liftAlongBase :
    liftAlongSection B S hS hi ≫ liftAlongBase B S hS i p = p ≫ i :=
  hom_ext_apply B S hS fun _ _ ↦ rfl

/-- Evaluating the morphism `b` of a pair at the identity and feeding the result back into the
comparison `W ⟶ Π_i W` returns the pair one started from. -/
theorem liftAlongSectionApp_lift_eq (T : BigFppfOver B S hS) (ξ : LiftAlong B S hS i p T)
    (v : I.obj.obj (Opposite.op T))
    (hv : i.hom.app (Opposite.op T) v = X.obj.map (𝟙 T).op ξ.base) :
    liftAlongSectionApp B S hS hi p T (ξ.lift T (𝟙 T) v hv) = ξ := by
  have hv' : i.hom.app (Opposite.op T) v = ξ.base := by
    rw [hv, op_id, Functor.map_id_apply]
  refine LiftAlong.ext _ _ ?_ fun T' t w h h' ↦ ?_
  · change i.hom.app (Opposite.op T) (p.hom.app (Opposite.op T) (ξ.lift T (𝟙 T) v hv)) = ξ.base
    rw [ξ.lift_proj T (𝟙 T) v hv]
    exact hv'
  · have hc : i.hom.app (Opposite.op T') (I.obj.map t.op v)
        = X.obj.map (t ≫ 𝟙 T).op ξ.base := by
      rw [app_map_op, hv', Category.comp_id]
    have hw : I.obj.map t.op v = w := by
      refine hi T' ?_
      rw [app_map_op, hv', h']
    exact (ξ.lift_map T T' t (𝟙 T) v hv hc).trans
      (LiftAlong.lift_congr rfl (Category.comp_id t) hw _ h')

section Cone

variable {Z : FppfSheaf B S hS} (a : Z ⟶ liftAlong B S hS i p) (b : Z ⟶ I)
  (hab : a ≫ liftAlongBase B S hS i p = b ≫ i)

include hab in
/-- For a commutative square `a ≫ liftAlongBase = b ≫ i`, the image under `i` of `b` evaluated at
a section `z` is the base of `a` evaluated at `z`. -/
theorem liftAlongCone_cond (T : BigFppfOver B S hS) (z : Z.obj.obj (Opposite.op T)) :
    i.hom.app (Opposite.op T) (b.hom.app (Opposite.op T) z)
      = X.obj.map (𝟙 T).op (a.hom.app (Opposite.op T) z).base := by
  have h := congrArg (fun k : Z ⟶ X ↦ k.hom.app (Opposite.op T) z) hab
  rw [comp_app_apply, comp_app_apply] at h
  exact h.symm.trans (by rw [op_id, Functor.map_id_apply]; rfl)

/-- The morphism to `W` induced by a cone over the square of
`AlgebraicGeometry.FormalSpace.DependentProduct.isPullback_liftAlongSection`: evaluate the
morphism `b` of the pair at the identity. -/
def liftAlongCone : Z ⟶ W :=
  ⟨{ app := fun T ↦ TypeCat.ofHom fun z ↦
       (a.hom.app T z).lift T.unop (𝟙 T.unop) (b.hom.app T z)
         (liftAlongCone_cond B S hS a b hab T.unop z)
     naturality := fun T T' r ↦ ConcreteCategory.hom_ext _ _ fun z ↦
       (LiftAlong.lift_eq_of_eq_restrict (a.hom.app T z) r.unop (a.hom.app T' (Z.obj.map r z))
           (NatTrans.naturality_apply a.hom r z) (by simp)
           (NatTrans.naturality_apply b.hom r z) _ _).trans
         ((a.hom.app T z).lift_map T.unop T'.unop r.unop (𝟙 T.unop) (b.hom.app T z) _
           (by rw [app_map_op, liftAlongCone_cond B S hS a b hab T.unop z,
             LiftAlong.map_comp_op_apply])).symm }⟩

/-- The morphism induced by a cone, composed with the comparison `W ⟶ Π_i W`, is `a`. -/
theorem liftAlongCone_comp_section :
    liftAlongCone B S hS a b hab ≫ liftAlongSection B S hS hi = a :=
  hom_ext_apply B S hS fun T z ↦
    liftAlongSectionApp_lift_eq B S hS hi T.unop (a.hom.app T z) (b.hom.app T z)
      (liftAlongCone_cond B S hS a b hab T.unop z)

/-- The morphism induced by a cone, composed with `p`, is `b`. -/
theorem liftAlongCone_comp_proj : liftAlongCone B S hS a b hab ≫ p = b :=
  hom_ext_apply B S hS fun T z ↦
    (a.hom.app T z).lift_proj T.unop (𝟙 T.unop) (b.hom.app T z) _

/-- A morphism `m : Z ⟶ W` whose composites with the comparison `W ⟶ Π_i W` and with `p` are `a`
and `b` is the morphism induced by the cone. -/
theorem liftAlongCone_unique (m : Z ⟶ W) (hm₁ : m ≫ liftAlongSection B S hS hi = a)
    (hm₂ : m ≫ p = b) : m = liftAlongCone B S hS a b hab := by
  refine hom_ext_apply B S hS fun T z ↦ ?_
  have h₁ := congrArg (fun k : Z ⟶ liftAlong B S hS i p ↦ k.hom.app T z) hm₁
  have h₂ := congrArg (fun k : Z ⟶ I ↦ k.hom.app T z) hm₂
  rw [comp_app_apply] at h₁ h₂
  refine Eq.trans ?_ (LiftAlong.lift_congr (ξ := liftAlongSectionApp B S hS hi p T.unop
    (m.hom.app T z)) h₁ rfl h₂ (by rw [op_id, Functor.map_id_apply]; rfl)
    (liftAlongCone_cond B S hS a b hab T.unop z))
  exact (Functor.map_id_apply W.obj _ _).symm

end Cone

/-- `W` is the fibre product `Π_i W ×_X I` when `i` is injective on sections: the square
formed by the comparison `W ⟶ Π_i W`, the structure morphism `p : W ⟶ I`, the morphism
`Π_i W ⟶ X` and `i : I ⟶ X` is cartesian. -/
theorem isPullback_liftAlongSection :
    IsPullback (liftAlongSection B S hS hi) p (liftAlongBase B S hS i p) i :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (liftAlongSection_comp_liftAlongBase B S hS hi)
    (fun s ↦ liftAlongCone B S hS s.fst s.snd s.condition)
    (fun s ↦ liftAlongCone_comp_section B S hS hi s.fst s.snd s.condition)
    (fun s ↦ liftAlongCone_comp_proj B S hS s.fst s.snd s.condition)
    (fun s m hm₁ hm₂ ↦ liftAlongCone_unique B S hS hi s.fst s.snd s.condition m hm₁ hm₂))



end Construction

/-! ### Functoriality of the dependent product -/

section Map

variable {W' : FppfSheaf B S hS} (i : I ⟶ X) {p : W ⟶ I} {p' : W' ⟶ I}
  (q : W ⟶ W') (hq : q ≫ p' = p)

include hq in
/-- Postcomposing the second component of a pair `(a, b)` with a morphism `W ⟶ W'` over `I`. -/
def LiftAlong.pushforward (T : BigFppfOver B S hS) (ξ : LiftAlong B S hS i p T) :
    LiftAlong B S hS i p' T where
  base := ξ.base
  lift T' t w h := q.hom.app (Opposite.op T') (ξ.lift T' t w h)
  lift_proj T' t w h := by
    rw [← comp_app_apply B S hS q p', hq]
    exact ξ.lift_proj T' t w h
  lift_map T' T'' s t w h h' := by
    rw [← app_map_op B S hS q s, ξ.lift_map T' T'' s t w h h']

/-- The dependent product on morphisms: a morphism `W ⟶ W'` over `I` induces
`Π_i W ⟶ Π_i W'` over `X`, by postcomposition on the second component. -/
def liftAlongMap : liftAlong B S hS i p ⟶ liftAlong B S hS i p' :=
  ⟨{ app := fun T ↦ TypeCat.ofHom (LiftAlong.pushforward B S hS i q hq T.unop)
     naturality := fun _ _ _ ↦ ConcreteCategory.hom_ext _ _ fun _ ↦
       LiftAlong.ext _ _ rfl fun _ _ _ _ _ ↦ rfl }⟩

/-- `liftAlongMap` depends on the morphism `q` only, not on the proof that it lies over `I`. -/
theorem liftAlongMap_congr {q₁ q₂ : W ⟶ W'} (hq₁₂ : q₁ = q₂) (h₁ : q₁ ≫ p' = p)
    (h₂ : q₂ ≫ p' = p) :
    liftAlongMap B S hS i q₁ h₁ = liftAlongMap B S hS i q₂ h₂ := by
  subst hq₁₂; rfl

/-- The morphism `Π_i W ⟶ Π_i W'` induced by `q` lies over `X`. -/
theorem liftAlongMap_comp_base :
    liftAlongMap B S hS i q hq ≫ liftAlongBase B S hS i p' = liftAlongBase B S hS i p :=
  hom_ext_apply B S hS fun _ _ ↦ rfl

/-- The dependent product preserves identities. -/
theorem liftAlongMap_id : liftAlongMap B S hS i (𝟙 W) (Category.id_comp p) = 𝟙 _ :=
  hom_ext_apply B S hS fun _ _ ↦ LiftAlong.ext _ _ rfl fun _ _ _ _ _ ↦ rfl

/-- The dependent product preserves composition. -/
theorem liftAlongMap_comp {W'' : FppfSheaf B S hS} {p'' : W'' ⟶ I} (q' : W' ⟶ W'')
    (hq' : q' ≫ p'' = p') :
    liftAlongMap B S hS i q hq ≫ liftAlongMap B S hS i q' hq'
      = liftAlongMap B S hS i (q ≫ q') (by rw [Category.assoc, hq', hq]) :=
  hom_ext_apply B S hS fun _ _ ↦ LiftAlong.ext _ _ rfl fun _ _ _ _ _ ↦ rfl

end Map

/-! ### The dependent product of the identity -/

section Identity

variable (i : I ⟶ X)

/-- The section of `Π_i I` over `T` attached to a section of `X`. Its lifting rule has no
choice: the condition `𝟙 ∘ b = a` on the fibre product forces `b` to be the identity. -/
def liftAlongIdApp (T : BigFppfOver B S hS) (a : X.obj.obj (Opposite.op T)) :
    LiftAlong B S hS i (𝟙 I) T where
  base := a
  lift _ _ w _ := w
  lift_proj _ _ _ _ := rfl
  lift_map _ _ _ _ _ _ _ := rfl

/-- The section of `Π_i I` attached to a section `a` of `X`, restricted along `r`, is the
section attached to the restriction of `a` along `r`. -/
theorem liftAlongIdApp_restrict {T T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (a : X.obj.obj (Opposite.op T)) :
    (liftAlongIdApp B S hS i T a).restrict r
      = liftAlongIdApp B S hS i T' (X.obj.map r.op a) :=
  LiftAlong.ext _ _ rfl fun _ _ _ _ _ ↦ rfl

/-- **The dependent product of the identity of `I` along `i : I ⟶ X` is `X` itself**, the
inverse of its structure morphism. The dependent product is right adjoint to the base change
along `i`, so it carries the terminal object of the sheaves over `I` to the terminal object of
the sheaves over `X`, which is `X`. -/
def liftAlongId : X ⟶ liftAlong B S hS i (𝟙 I) :=
  ⟨{ app := fun T ↦ TypeCat.ofHom (liftAlongIdApp B S hS i T.unop)
     naturality := fun _ _ r ↦ ConcreteCategory.hom_ext _ _ fun a ↦
       (liftAlongIdApp_restrict B S hS i r.unop a).symm }⟩

/-- The composite `X ⟶ Π_i I ⟶ X` is the identity. -/
theorem liftAlongId_comp_liftAlongBase :
    liftAlongId B S hS i ≫ liftAlongBase B S hS i (𝟙 I) = 𝟙 X :=
  hom_ext_apply B S hS fun _ _ ↦ rfl

/-- The composite `Π_i I ⟶ X ⟶ Π_i I` is the identity. -/
theorem liftAlongBase_comp_liftAlongId :
    liftAlongBase B S hS i (𝟙 I) ≫ liftAlongId B S hS i
      = 𝟙 (liftAlong B S hS i (𝟙 I)) := by
  refine hom_ext_apply B S hS fun T ξ ↦ ?_
  change liftAlongIdApp B S hS i T.unop ξ.base = ξ
  refine LiftAlong.ext _ _ rfl fun T' t w h h' ↦ ?_
  change w = ξ.lift T' t w h'
  simpa using (ξ.lift_proj T' t w h').symm

/-- **The structure morphism of the dependent product of the identity is an isomorphism.** -/
instance isIso_liftAlongBase_id : IsIso (liftAlongBase B S hS i (𝟙 I)) :=
  ⟨liftAlongId B S hS i, liftAlongBase_comp_liftAlongId B S hS i,
    liftAlongId_comp_liftAlongBase B S hS i⟩

end Identity
end AlgebraicGeometry.FormalSpace.DependentProduct

end
