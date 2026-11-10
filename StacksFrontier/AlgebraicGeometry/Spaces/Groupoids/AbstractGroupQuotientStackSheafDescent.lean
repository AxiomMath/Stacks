module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientInertia
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackIsStack
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.StackOfTorsors
public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulGroupoidDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective

/-!
# `[[X/G]]` is a stack for a sheaf `X` in any universe (Stacks 0371)

Let `S` be a scheme of a big fppf site `B`, let `G` be an abstract group and let `X` be a sheaf
on `(Sch/S)_fppf` with an action `ρ : G →* Aut X`. The quotient `[[X/G]]` of Stacks 0371
(`AlgebraicGeometry.AbstractGroupQuotientStack`) is a stack over `(Sch/S)_fppf` as soon as its
torsors have sections in a universe at least that of the objects of the site, whatever the
universe of the values of `X`. The case where `X` takes values in that same universe is
`AlgebraicGeometry.AbstractGroupQuotientStack.projection_isStack_of_isSheaf`.

## Implementation notes

The result is Stacks 0CKJ applied to the faithful functor
`AlgebraicGeometry.AbstractGroupQuotientStack.forget` to the torsors of Stacks 04UJ. The
separation half is `AlgebraicGeometry.AbstractGroupQuotientStack.forget_hsep`; the glueing half
glues the equivariant maps of a descent datum along the restriction of the glued torsor
(`AlgebraicGeometry.AbstractGroupQuotientStack.pullback`).

## Main definitions

* `AlgebraicGeometry.AbstractGroupQuotientStack.pullback`, `.pullbackHom`: the restriction of an
  object along a morphism of the site and its morphism to the object.

## Main results

* `AlgebraicGeometry.AbstractGroupQuotientStack.hglue_forget`: the glueing half of the descent
  along `[[X/G]] ⥤ 𝒢-Torsors`.
* `AlgebraicGeometry.AbstractGroupQuotientStack.projection_isStack`: `[[X/G]]` is a stack.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace AbstractGroupQuotientStack

universe t z w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {G : Type w} [Group G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type z} {ρ : G →* Aut X}

/-- The torsor underlying an object of `[[X/G]]` lives over the base of that object. -/
@[simp] lemma toTorsors_base (A : AbstractGroupQuotientStack.{t} B S hS G X ρ) :
    A.toTorsors.base = A.base := rfl

/-- The morphism of the site recorded by a composite is the composite of the recorded
morphisms. -/
@[simp] lemma comp_base {A A' A'' : AbstractGroupQuotientStack.{t} B S hS G X ρ} (m : A ⟶ A')
    (m' : A' ⟶ A'') : (m ≫ m').base = m.base ≫ m'.base := rfl

/-- The map on total spaces of a composite is the composite of the maps on total spaces. -/
@[simp] lemma comp_map {A A' A'' : AbstractGroupQuotientStack.{t} B S hS G X ρ} (m : A ⟶ A')
    (m' : A' ⟶ A'') (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) :
    (m ≫ m').map V p = m'.map V (m.map V p) := rfl

/-- The identity of an object records the identity of its base. -/
@[simp] lemma id_base (A : AbstractGroupQuotientStack.{t} B S hS G X ρ) :
    Hom.base (𝟙 A) = 𝟙 A.base := rfl

/-- The identity of an object is the identity on total spaces. -/
@[simp] lemma id_map (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) : Hom.map (𝟙 A) V p = p := rfl

/-- The projection to the site sends a morphism to the morphism of the site it records. -/
@[simp] lemma projection_map' {A A' : AbstractGroupQuotientStack.{t} B S hS G X ρ}
    (m : A ⟶ A') : projection.map m = m.base := rfl

/-- The restriction of an object `(U, P, φ)` of `[[X/G]]` along a morphism `f : V ⟶ U` of the
site: the restricted torsor `f^{-1}P` with the restricted map to `X`. -/
def pullback (A : AbstractGroupQuotientStack.{t} B S hS G X ρ) {V : BigFppfOver B S hS}
    (f : V ⟶ A.base) : AbstractGroupQuotientStack.{t} B S hS G X ρ where
  base := V
  torsor := ((forget.obj A).pullback f).torsor
  isTorsor := ((forget.obj A).pullback f).isTorsor
  toTarget W s := A.toTarget (op ((Over.map f).obj W.unop)) s
  toTarget_naturality h s := A.toTarget_naturality ((Over.map f).op.map h) s
  toTarget_equivariant W g s := A.toTarget_equivariant (op ((Over.map f).obj W.unop)) g s

/-- The torsor underlying the restriction of an object is the restriction of its torsor. -/
lemma forget_obj_pullback (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    {V : BigFppfOver B S hS} (f : V ⟶ A.base) :
    forget.obj (A.pullback f) = (forget.obj A).pullback f := rfl

/-- The morphism from the restriction of an object of `[[X/G]]` to the object. -/
def pullbackHom (A : AbstractGroupQuotientStack.{t} B S hS G X ρ) {V : BigFppfOver B S hS}
    (f : V ⟶ A.base) : A.pullback f ⟶ A where
  base := f
  map := ((forget.obj A).pullbackHom f).map
  map_naturality := ((forget.obj A).pullbackHom f).map_naturality
  map_equivariant := ((forget.obj A).pullbackHom f).map_equivariant
  bijOn_map := ((forget.obj A).pullbackHom f).bijOn_map
  totalToTarget_comp _ _ := rfl

/-- The morphism of torsors underlying `pullbackHom` is the morphism from the restricted
torsor. -/
lemma forget_map_pullbackHom (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    {V : BigFppfOver B S hS} (f : V ⟶ A.base) :
    forget.map (A.pullbackHom f) = (forget.obj A).pullbackHom f := rfl

/-! ### `[[X/G]]` is a stack -/

section Stack

variable (B S hS G) in
/-- **Stacks 04UK** for the constant sheaf of groups on `(Sch/S)_fppf`, in the sieve-theoretic
form of Stacks 026F: the torsors under it, with sections in a universe at least that of the
objects of the site, form a stack. -/
theorem torsors_isStack :
    (SheafOfGroups.Torsors.projection :
      SheafOfGroups.Torsors.{max (u + 1) t} (bigConstantGroupSheaf B S hS G) ⥤
        BigFppfOver B S hS).IsStack (BigFppfOver.topology B S hS) := by
  have : (SheafOfGroups.Torsors.projection :
      SheafOfGroups.Torsors.{max (u + 1) t} (bigConstantGroupSheaf B S hS G) ⥤ _).IsFibered :=
    SheafOfGroups.Torsors.projection_isFiberedInGroupoids.isFibered
  exact Functor.isStack_of_isStackInGroupoids
    (SheafOfGroups.Torsors.projection_isStackInGroupoids.{t, w, u, u + 1, u + 1})

/-- A morphism of torsors lying over a morphism `a` of the site records `a`, conjugated by the
identifications of the bases. -/
lemma torsors_base_of_isHomLift {T T' : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)}
    {V W : BigFppfOver B S hS} (a : V ⟶ W) (m : T ⟶ T')
    (hm : SheafOfGroups.Torsors.projection.IsHomLift a m) (hT : T.base = V) (hT' : T'.base = W) :
    SheafOfGroups.Torsors.Hom.base m = eqToHom hT ≫ a ≫ eqToHom hT'.symm := by
  have := hm
  exact IsHomLift.fac' SheafOfGroups.Torsors.projection a m

/-- A morphism of `[[X/G]]` lying over a morphism `a` of the site records `a`, conjugated by the
identifications of the bases. -/
lemma base_of_isHomLift {A A' : AbstractGroupQuotientStack.{t} B S hS G X ρ}
    {V W : BigFppfOver B S hS} (a : V ⟶ W) (m : A ⟶ A') (hm : projection.IsHomLift a m)
    (hA : A.base = V) (hA' : A'.base = W) :
    m.base = eqToHom hA ≫ a ≫ eqToHom hA'.symm := by
  have := hm
  exact IsHomLift.fac' projection a m

/-- A morphism of `[[X/G]]` whose recorded morphism of the site is `a`, conjugated by
identifications of the bases, lies over `a`. -/
lemma isHomLift_of_base {A A' : AbstractGroupQuotientStack.{t} B S hS G X ρ}
    {V W : BigFppfOver B S hS} (a : V ⟶ W) (m : A ⟶ A') (hA : A.base = V) (hA' : A'.base = W)
    (h : m.base = eqToHom hA ≫ a ≫ eqToHom hA'.symm) : projection.IsHomLift a m :=
  IsHomLift.of_fac' projection a m hA hA' h

/-- The variant of `AlgebraicGeometry.AbstractGroupQuotientStack.isHomLift_of_base` with the
target of `a` the base of the target object. -/
lemma isHomLift_of_base' {A A' : AbstractGroupQuotientStack.{t} B S hS G X ρ}
    {V : BigFppfOver B S hS} (a : V ⟶ A'.base) (m : A ⟶ A') (hA : A.base = V)
    (h : m.base = eqToHom hA ≫ a) : projection.IsHomLift a m :=
  isHomLift_of_base a m hA rfl (by simpa using h)

/-- Two morphisms of torsors with a common target lying over the same morphism of the site and
agreeing after composition with a morphism to the common target are equal: the torsors form a
category fibred in groupoids. -/
lemma torsors_hom_ext {T T' T'' : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)}
    (m m' : T ⟶ T') (φ : T' ⟶ T'')
    (hb : SheafOfGroups.Torsors.Hom.base m = SheafOfGroups.Torsors.Hom.base m')
    (h : m ≫ φ = m' ≫ φ) : m = m' := by
  obtain ⟨χ, -, hχ⟩ :=
    (SheafOfGroups.Torsors.projection_isFiberedInGroupoids
      (𝒢 := bigConstantGroupSheaf B S hS G)).unique_lift
      φ (m' ≫ φ) (SheafOfGroups.Torsors.Hom.base m') rfl
  exact (hχ m ⟨hb, h⟩).trans (hχ m' ⟨rfl, rfl⟩).symm

/-! ### The glueing half of the descent along `[[X/G]] ⥤ Torsors` -/

section Glue

variable {y : SheafOfGroups.Torsors.{max (u + 1) t} (bigConstantGroupSheaf B S hS G)}
  {V : BigFppfOver B S hS} (h : V ⟶ y.base) {R : Sieve V}
  (x : ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V), R g →
    AbstractGroupQuotientStack.{max (u + 1) t} B S hS G X ρ)
  (f : ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g), forget.obj (x g hg) ⟶ y)
  (hf : ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g),
    SheafOfGroups.Torsors.projection.IsHomLift (g ≫ h) (f g hg))

include hf in
/-- The object `x g` lies over the source `W` of the member `g` of the sieve. -/
lemma glue_base {W : BigFppfOver B S hS} (g : W ⟶ V) (hg : R g) : (x g hg).base = W := by
  have := hf g hg
  exact IsHomLift.domain_eq SheafOfGroups.Torsors.projection (g ≫ h) (f g hg)

/-- The morphism of the site recorded by `f g` is `g ≫ h`, up to the identification of the
base of `x g` with `W`. -/
lemma glue_fbase {W : BigFppfOver B S hS} (g : W ⟶ V) (hg : R g) :
    SheafOfGroups.Torsors.Hom.base (f g hg) = eqToHom (glue_base h x f hf g hg) ≫ g ≫ h := by
  rw [torsors_base_of_isHomLift (g ≫ h) (f g hg) (hf g hg) (glue_base h x f hf g hg) rfl]
  simp

/-- A section `q` of `y` over `g ≫ h` has a unique preimage under `f g` among the sections of
the torsor of `x g` over the identity of its base. -/
lemma glue_pre {W : BigFppfOver B S hS} (g : W ⟶ V) (hg : R g) (q : y.Total (op W))
    (hq : q.1 = g ≫ h) :
    ∃! p : (x g hg).Total (op W), p.1 = eqToHom (glue_base h x f hf g hg).symm ∧
      (f g hg).map (op W) p = q :=
  (f g hg).existsUnique_map _ q (by rw [hq, glue_fbase h x f hf]; simp)

/-- The local value of the glued map at a section `q` of `y` over a member `g` of the sieve: the
value of the equivariant map of `x g` at the section of its torsor corresponding to `q`. -/
def glueVal {W : BigFppfOver B S hS} (g : W ⟶ V) (hg : R g) (q : y.Total (op W))
    (hq : q.1 = g ≫ h) : X.obj (op W) :=
  (x g hg).totalToTarget (op W) (glue_pre h x f hf g hg q hq).exists.choose

/-- The local value at `q` is the value of the equivariant map of `x g` at any preimage of `q`
under `f g` over the identity of the base. -/
lemma glueVal_eq {W : BigFppfOver B S hS} (g : W ⟶ V) (hg : R g) (q : y.Total (op W))
    (hq : q.1 = g ≫ h) (p : (x g hg).Total (op W))
    (hp₁ : p.1 = eqToHom (glue_base h x f hf g hg).symm) (hp₂ : (f g hg).map (op W) p = q) :
    glueVal h x f hf g hg q hq = (x g hg).totalToTarget (op W) p :=
  congrArg ((x g hg).totalToTarget (op W))
    ((glue_pre h x f hf g hg q hq).unique (glue_pre h x f hf g hg q hq).exists.choose_spec
      ⟨hp₁, hp₂⟩)

/-- The local value depends only on the member of the sieve and the section, not on the
proofs. -/
lemma glueVal_congr {W : BigFppfOver B S hS} {g g' : W ⟶ V} (e : g = g') (hg : R g) (hg' : R g')
    {q q' : y.Total (op W)} (eq : q = q') (hq : q.1 = g ≫ h) (hq' : q'.1 = g' ≫ h) :
    glueVal h x f hf g hg q hq = glueVal h x f hf g' hg' q' hq' := by
  subst e
  subst eq
  rfl

variable (hc : ∀ ⦃W W' : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g) (k : W' ⟶ W),
    ∃ c : x (k ≫ g) (R.downward_closed hg k) ⟶ x g hg,
      projection.IsHomLift k c ∧ forget.map c ≫ f g hg = f (k ≫ g) (R.downward_closed hg k))

include hc in
/-- The local value at the image under `f g` of a section of the torsor of `x g` over `k`, read
through the member `k ≫ g` of the sieve, is the value of the equivariant map of `x g`. -/
lemma glueVal_transfer {W W' : BigFppfOver B S hS} (g : W ⟶ V) (hg : R g) (k : W' ⟶ W)
    (p : (x g hg).Total (op W')) (hp : p.1 = k ≫ eqToHom (glue_base h x f hf g hg).symm) :
    glueVal h x f hf (k ≫ g) (R.downward_closed hg k) ((f g hg).map (op W') p) (by
      refine ((f g hg).fst_map (V := op W') p).trans ?_
      rw [glue_fbase h x f hf]
      change p.1 ≫ _ = _
      rw [hp]
      simp) = (x g hg).totalToTarget (op W') p := by
  obtain ⟨c, hcl, hcf⟩ := hc g hg k
  have hcb := base_of_isHomLift k c hcl (glue_base h x f hf (k ≫ g) (R.downward_closed hg k))
    (glue_base h x f hf g hg)
  obtain ⟨p', hp'₁, hp'₂⟩ := (c.bijOn_map (op W')
    (eqToHom (glue_base h x f hf (k ≫ g) (R.downward_closed hg k)).symm)).surjOn
    (show p.1 = _ ≫ c.base by rw [hp, hcb]; simp)
  refine (glueVal_eq h x f hf (k ≫ g) _ _ _ p' hp'₁ ?_).trans ?_
  · rw [← hcf]
    change (f g hg).map (op W') (c.map (op W') p') = _
    rw [hp'₂]
  · rw [← c.totalToTarget_comp, hp'₂]

include hc in
/-- The local values are compatible with restriction: the value at the restriction of `q` along
`k` is the restriction along `k` of the value at `q`. -/
lemma glueVal_restrict {W W' : BigFppfOver B S hS} (g : W ⟶ V) (hg : R g) (k : W' ⟶ W)
    (q : y.Total (op W)) (hq : q.1 = g ≫ h) :
    glueVal h x f hf (k ≫ g) (R.downward_closed hg k) (y.totalMap k.op q)
      (by change k ≫ q.1 = _; rw [hq]; simp) =
      X.map k.op (glueVal h x f hf g hg q hq) := by
  obtain ⟨p, ⟨hp₁, hp₂⟩, -⟩ := glue_pre h x f hf g hg q hq
  have hpq := glueVal_eq h x f hf g hg q hq p hp₁ hp₂
  rw [hpq, ← totalToTarget_naturality]
  rw [← glueVal_transfer h x f hf hc g hg k ((x g hg).totalMap k.op p) (by
    change k ≫ p.1 = _
    rw [hp₁])]
  refine glueVal_congr h x f hf rfl _ _ ?_ _ _
  rw [← hp₂]
  exact ((f g hg).map_naturality k.op p).symm

/-- The local values are equivariant: the value at `g' • q` is the action of `ρ g'` on the
value at `q`. -/
lemma glueVal_totalSmul {W : BigFppfOver B S hS} (g : W ⟶ V) (hg : R g) (g' : G)
    (q : y.Total (op W)) (hq : q.1 = g ≫ h) :
    glueVal h x f hf g hg
      (y.totalSmul (constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G (op W) g') q)
      hq = (ρ g').asIso.hom.app (op W) (glueVal h x f hf g hg q hq) := by
  obtain ⟨p, ⟨hp₁, hp₂⟩, -⟩ := glue_pre h x f hf g hg q hq
  rw [glueVal_eq h x f hf g hg q hq p hp₁ hp₂, ← totalToTarget_totalSmul]
  refine glueVal_eq h x f hf g hg _ _ _ hp₁ ?_
  rw [← hp₂]
  exact (f g hg).map_equivariant (op W) _ p

variable (hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
  (hR : R ∈ (BigFppfOver.topology B S hS) V)

/-- The family of local values attached to a section of the restriction `h^{-1}y` over an object
`W` of `(Sch/S)_fppf/V`, on the pullback of the sieve to `W`. -/
def glueFamily (W : (Over V)ᵒᵖ) (s : (y.pullback h).torsor.presheaf.obj W) :
    Presieve.FamilyOfElements X (R.pullback W.unop.hom).arrows :=
  fun Z k hk => glueVal h x f hf (k ≫ W.unop.hom) hk
    (y.totalMap k.op (⟨W.unop.hom ≫ h, s⟩ : y.Total (op W.unop.left)))
    (by change k ≫ W.unop.hom ≫ h = _; simp)

include hc in
/-- The family of local values is compatible. -/
lemma glueFamily_compatible (W : (Over V)ᵒᵖ) (s : (y.pullback h).torsor.presheaf.obj W) :
    (glueFamily h x f hf W s).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z k l hk
  refine Eq.trans ?_ (glueVal_restrict h x f hf hc (k ≫ W.unop.hom) hk l _ _)
  refine glueVal_congr h x f hf (Category.assoc _ _ _) _ _ ?_ _ _
  exact (SheafOfGroups.Torsors.totalMap_comp y k.op l.op _).symm

/-- The glued equivariant map on the restriction `h^{-1}y`. -/
def glueMap (W : (Over V)ᵒᵖ) (s : (y.pullback h).torsor.presheaf.obj W) : X.obj (op W.unop.left) :=
  (hX _ ((BigFppfOver.topology B S hS).pullback_stable W.unop.hom hR)).amalgamate
    (glueFamily h x f hf W s) (glueFamily_compatible h x f hf hc W s)

/-- The restriction of the glued map along a member `k` of the pulled-back sieve is the local
value along `k`. -/
lemma glueMap_restrict (W : (Over V)ᵒᵖ) (s : (y.pullback h).torsor.presheaf.obj W)
    {Z : BigFppfOver B S hS} (k : Z ⟶ W.unop.left) (hk : R (k ≫ W.unop.hom)) :
    X.map k.op (glueMap h x f hf hc hX hR W s) = glueFamily h x f hf W s k hk :=
  (hX _ ((BigFppfOver.topology B S hS).pullback_stable W.unop.hom hR)).valid_glue
    (glueFamily_compatible h x f hf hc W s) k hk

/-- The glued object of `[[X/G]]`: the restriction `h^{-1}y` of the torsor with the glued map. -/
def glueObj : AbstractGroupQuotientStack.{max (u + 1) t} B S hS G X ρ where
  base := V
  torsor := (y.pullback h).torsor
  isTorsor := (y.pullback h).isTorsor
  toTarget := glueMap h x f hf hc hX hR
  toTarget_naturality {W₁ W₂} m s := by
    refine (hX _ ((BigFppfOver.topology B S hS).pullback_stable W₂.unop.hom hR)
      ).isSeparatedFor.ext (fun Z k hk => ?_)
    have hk' : R ((k ≫ m.unop.left) ≫ W₁.unop.hom) := by
      rw [Category.assoc, Over.w m.unop]
      exact hk
    refine (glueMap_restrict h x f hf hc hX hR W₂ _ k hk).trans
      (Eq.trans ?_ (X.map_comp_apply (m.unop.left).op k.op _))
    refine Eq.trans ?_ (glueMap_restrict h x f hf hc hX hR W₁ s (k ≫ m.unop.left) hk').symm
    refine glueVal_congr h x f hf (by rw [Category.assoc, Over.w m.unop]) _ _ ?_ _ _
    refine Eq.trans ?_ (SheafOfGroups.Torsors.totalMap_comp y m.unop.left.op k.op _)
    exact congrArg (y.totalMap k.op) (SheafOfGroups.Torsors.totalMap_mk y m.unop.left.op
      (by simp only [Quiver.Hom.unop_op]; rw [← Category.assoc, Over.w m.unop]; rfl)
      ((Over.map h).map m.unop) rfl s).symm
  toTarget_equivariant W g' s := by
    refine (hX _ ((BigFppfOver.topology B S hS).pullback_stable W.unop.hom hR)
      ).isSeparatedFor.ext (fun Z k hk => ?_)
    rw [glueMap_restrict h x f hf hc hX hR W _ k hk, ← NatTrans.naturality_apply,
      glueMap_restrict h x f hf hc hX hR W s k hk]
    refine Eq.trans ?_ (glueVal_totalSmul h x f hf (k ≫ W.unop.hom) hk g' _ _)
    refine glueVal_congr h x f hf rfl _ _ ?_ _ _
    refine (SheafOfGroups.Torsors.totalMap_totalSmul y k.op _
      (⟨W.unop.hom ≫ h, s⟩ : y.Total (op W.unop.left))).trans ?_
    rw [constantSheafOfGroupsUnit_naturality]

/-- Over a member `b` of the sieve, the glued map is the local value along `b`. -/
lemma glueMap_eq {Wo : BigFppfOver B S hS} (b : Wo ⟶ V) (hb : R b)
    (s : (y.pullback h).torsor.presheaf.obj (op (Over.mk b))) :
    glueMap h x f hf hc hX hR (op (Over.mk b)) s =
      glueVal h x f hf b hb (⟨b ≫ h, s⟩ : y.Total (op Wo)) rfl := by
  have hmem : R (𝟙 Wo ≫ b) := (congrArg (fun φ => R.arrows φ) (Category.id_comp b)).mpr hb
  refine (X.map_id_apply _ _).symm.trans ?_
  refine (glueMap_restrict h x f hf hc hX hR (op (Over.mk b)) s (𝟙 Wo) hmem).trans ?_
  exact glueVal_congr h x f hf (Category.id_comp b) _ _
    (SheafOfGroups.Torsors.totalMap_id y _) _ _

/-- The torsor underlying the glued object is the restriction `h^{-1}y`. -/
lemma forget_obj_glueObj : forget.obj (glueObj h x f hf hc hX hR) = y.pullback h := rfl

include hc in
/-- Each `x g` has a morphism to the glued object lying over `g` whose underlying morphism of
torsors, composed with the morphism from `h^{-1}y` to `y`, is `f g`. -/
lemma exists_glueHom {W : BigFppfOver B S hS} (g : W ⟶ V) (hg : R g) :
    ∃ c : x g hg ⟶ glueObj h x f hf hc hX hR,
      projection.IsHomLift g c ∧ forget.map c ≫ y.pullbackHom h = f g hg := by
  obtain ⟨c₀, ⟨hc₀b, hc₀c⟩, -⟩ :=
    (SheafOfGroups.Torsors.projection_isFiberedInGroupoids
      (𝒢 := bigConstantGroupSheaf B S hS G)).unique_lift
      (y.pullbackHom h) (f g hg) (eqToHom (glue_base h x f hf g hg) ≫ g) (by
        change (eqToHom (glue_base h x f hf g hg) ≫ g) ≫ h =
          SheafOfGroups.Torsors.Hom.base (f g hg)
        rw [glue_fbase h x f hf]
        simp)
  have hc₀b' : SheafOfGroups.Torsors.Hom.base c₀ = eqToHom (glue_base h x f hf g hg) ≫ g :=
    hc₀b
  refine ⟨homOfTorsorHom c₀ (fun Wo p => ?_),
    isHomLift_of_base' (A' := glueObj h x f hf hc hX hR) g _ (glue_base h x f hf g hg) hc₀b',
    hc₀c⟩
  have hr₁ : (c₀.map Wo p).1 = (p.1 ≫ eqToHom (glue_base h x f hf g hg)) ≫ g :=
    (c₀.fst_map (V := Wo) p).trans (by rw [hc₀b', Category.assoc]; rfl)
  have key : ∀ q : (y.pullback h).Total Wo, q = c₀.map Wo p →
      (glueObj h x f hf hc hX hR).totalToTarget Wo q = (x g hg).totalToTarget Wo p := by
    rintro ⟨b, s⟩ hq
    have hb : b = (p.1 ≫ eqToHom (glue_base h x f hf g hg)) ≫ g :=
      (congrArg Sigma.fst hq).trans hr₁
    have hbR : R b := (congrArg (fun φ => R.arrows φ) hb).mpr (R.downward_closed hg _)
    have hfq : (⟨b ≫ h, s⟩ : y.Total Wo) = (f g hg).map Wo p := by
      have e := congrFun (congrFun (congrArg SheafOfGroups.Torsors.Hom.map hc₀c) Wo) p
      refine Eq.trans ?_ e
      change _ = (y.pullbackHom h).map Wo (c₀.map Wo p)
      rw [← hq]
      rfl
    refine (glueMap_eq h x f hf hc hX hR b hbR s).trans ?_
    refine (glueVal_congr h x f hf hb hbR (R.downward_closed hg _) hfq rfl
      (by rw [← hfq]; exact congrArg (· ≫ h) hb)).trans ?_
    exact glueVal_transfer h x f hf hc g hg (p.1 ≫ eqToHom (glue_base h x f hf g hg)) p
      (by simp)
  exact key _ rfl

end Glue

/-- **The glueing half of the descent along `[[X/G]] ⥤ Torsors`.** -/
lemma hglue_forget (hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) :
    ∀ (y : SheafOfGroups.Torsors.{max (u + 1) t} (bigConstantGroupSheaf B S hS G))
      ⦃V : BigFppfOver B S hS⦄
      (h : V ⟶ SheafOfGroups.Torsors.projection.obj y) (R : Sieve V),
      R ∈ (BigFppfOver.topology B S hS) V →
      ∀ (x : ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V), R g →
          AbstractGroupQuotientStack.{max (u + 1) t} B S hS G X ρ)
        (f : ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g), forget.obj (x g hg) ⟶ y),
        (∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g),
          SheafOfGroups.Torsors.projection.IsHomLift (g ≫ h) (f g hg)) →
        (∀ ⦃W W' : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g) (k : W' ⟶ W),
          ∃ c : x (k ≫ g) (R.downward_closed hg k) ⟶ x g hg,
            projection.IsHomLift k c ∧
              forget.map c ≫ f g hg = f (k ≫ g) (R.downward_closed hg k)) →
        ∃ (x₀ : AbstractGroupQuotientStack.{max (u + 1) t} B S hS G X ρ)
          (f₀ : forget.obj x₀ ⟶ y), SheafOfGroups.Torsors.projection.IsHomLift h f₀ ∧
          ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g), ∃ c : x g hg ⟶ x₀,
            projection.IsHomLift g c ∧ forget.map c ≫ f₀ = f g hg := by
  intro y V h R hR x f hf hc
  change V ⟶ y.base at h
  refine ⟨glueObj h x f hf hc hX hR, y.pullbackHom h,
    SheafOfGroups.Torsors.isHomLift_of_base _ (y.pullbackHom_base h), fun W g hg => ?_⟩
  exact exists_glueHom h x f hf hc hX hR g hg

/-- **Stacks 0371.** Let `X` be a sheaf on `(Sch/S)_fppf` with an action of the abstract group
`G`. Then `[[X/G]]`, with torsors whose sections lie in a universe at least that of the objects
of the site, is a stack over `(Sch/S)_fppf`. It is fibred in groupoids by
`AlgebraicGeometry.AbstractGroupQuotientStack.projection_isFiberedInGroupoids`. -/
theorem projection_isStack (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) :
    (projection : AbstractGroupQuotientStack.{max (u + 1) t} B S hS G X ρ ⥤ _).IsStack
      (BigFppfOver.topology B S hS) := by
  have hX' := (isSheaf_iff_isSheaf_of_type _ X).mp hX
  exact Functor.isStack_of_faithful_of_isSheaf projection_isFiberedInGroupoids
    SheafOfGroups.Torsors.projection_isFiberedInGroupoids forget_comp_projection
    (torsors_isStack B S hS G) (fun _ => inferInstance)
    (fun y _ h R hR _ _ f f' hlf hlf' hloc => forget_hsep hX y h R hR f f' hlf hlf' hloc)
    (hglue_forget hX')

end Stack

end AbstractGroupQuotientStack

end AlgebraicGeometry
