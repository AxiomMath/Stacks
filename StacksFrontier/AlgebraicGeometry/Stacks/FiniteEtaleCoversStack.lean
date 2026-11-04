module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteEtaleCovers

/-!
# Gluing morphisms of finite étale covers over the big fppf site

Let `S` be a scheme contained in a big fppf site, let `FÉt` be the category of finite étale
covers of Stacks 0BLY and let `p : FÉt ⟶ (Sch/S)_fppf` be its projection to the base. This
file proves condition (2) of Stacks 026F for `p`: the presheaves `Mor(x, y)` of Stacks 02ZB
are sheaves for the fppf topology.

The separatedness half is `AlgebraicGeometry.finiteEtaleProjection_eq_of_locallyEqual`. What
is proved here is the gluing half: a family of morphisms `W ⟶ b` indexed by the morphisms
`W ⟶ a` of `FÉt` lying over a covering sieve of `a.right`, compatible with composition and
lying over a fixed morphism `u` of bases, comes from a single morphism `a ⟶ b` over `u`.

## Main definitions

* `AlgebraicGeometry.finiteEtaleBaseChangeFactor`: the factorisation of a morphism of `FÉt`
  through a base change of its target along a factorisation of its morphism of bases.
* `AlgebraicGeometry.finiteEtaleBaseChangeSection`: the section of the base change of a cover
  `a` along `k ≫ a.hom` attached to a morphism `k` into the total space of `a`.

## Main results

* `AlgebraicGeometry.finiteEtaleProjection_exists_glue`: the gluing half of condition (2) of
  Stacks 026F for `FÉt`.
* `AlgebraicGeometry.finiteEtaleProjection_isMorSheaf`: condition (2) of Stacks 026F for
  `FÉt`.

## Implementation notes

The total space of a finite étale cover is an object of the site, so the morphisms out of it
form a representable presheaf, which is a sheaf because the fppf topology is subcanonical.
The left leg of the glued morphism `a ⟶ b` is produced by gluing over the pullback of the
given covering sieve along `a.hom`, a covering sieve of `a.left`; the family glued there is
indexed by the morphisms `k` into `a.left`, and its member at `k` is the given morphism at
the base change of `a` along `k ≫ a.hom`, restricted along the canonical section of that
base change. Every compatibility to be checked is then an equality of two morphisms into a
fibre product, so it is settled by the two projections.

## References

* [Stacks Project, Tag 0BLZ](https://stacks.math.columbia.edu/tag/0BLZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Factorisations through a base change -/

/-- A morphism into the total space of a base change of `a` is determined by its two
projections, to the total space of `a` and to the new base. -/
lemma finiteEtaleBaseChange_left_hom_ext (a : FiniteEtaleCovers B S hS)
    {V W : BigFppfOver B S hS} (h : W ⟶ a.right)
    {t t' : V ⟶ (FiniteEtaleCovers.baseChange B S hS a h).left}
    (hfst : t ≫ pullback.fst a.hom h = t' ≫ pullback.fst a.hom h)
    (hsnd : t ≫ pullback.snd a.hom h = t' ≫ pullback.snd a.hom h) :
    t = t' :=
  pullback.hom_ext hfst hsnd

/-- The structure morphism of the base change of `a` along `h` is the second projection. -/
@[simp]
lemma finiteEtaleBaseChange_hom (a : FiniteEtaleCovers B S hS) {W : BigFppfOver B S hS}
    (h : W ⟶ a.right) :
    (FiniteEtaleCovers.baseChange B S hS a h).hom = pullback.snd a.hom h := rfl

/-- The morphism of total spaces of the base change morphism of `a` along `h` is the first
projection. -/
@[simp]
lemma finiteEtaleBaseChangeHom_left (a : FiniteEtaleCovers B S hS) {W : BigFppfOver B S hS}
    (h : W ⟶ a.right) :
    (FiniteEtaleCovers.baseChangeHom B S hS a h).left = pullback.fst a.hom h := rfl

/-- A morphism `Φ : x ⟶ a` of `FÉt` whose morphism of bases factors as `Φ.right = g ≫ h`
factors through the base change of `a` along `h`, by `g` on bases. -/
noncomputable def finiteEtaleBaseChangeFactor {x a : FiniteEtaleCovers B S hS} (Φ : x ⟶ a)
    {V : BigFppfOver B S hS} (h : V ⟶ a.right) (g : x.right ⟶ V) (hg : Φ.right = g ≫ h) :
    x ⟶ FiniteEtaleCovers.baseChange B S hS a h :=
  MorphismProperty.Arrow.homMk
    (FiniteEtaleCovers.baseChangeLift B S hS a h Φ.left (x.hom ≫ g)
      (by rw [MorphismProperty.Arrow.w Φ, hg, Category.assoc]))
    g
    (FiniteEtaleCovers.baseChangeLift_comp_snd B S hS a h Φ.left (x.hom ≫ g)
      (by rw [MorphismProperty.Arrow.w Φ, hg, Category.assoc]))

/-- The factorisation of `Φ` through the base change along `h` is `g` on bases. -/
@[simp]
lemma finiteEtaleBaseChangeFactor_right {x a : FiniteEtaleCovers B S hS} (Φ : x ⟶ a)
    {V : BigFppfOver B S hS} (h : V ⟶ a.right) (g : x.right ⟶ V) (hg : Φ.right = g ≫ h) :
    (finiteEtaleBaseChangeFactor B S hS Φ h g hg).right = g := rfl

/-- The factorisation of `Φ` followed by the first projection is `Φ.left`. -/
@[simp]
lemma finiteEtaleBaseChangeFactor_left_comp_fst {x a : FiniteEtaleCovers B S hS} (Φ : x ⟶ a)
    {V : BigFppfOver B S hS} (h : V ⟶ a.right) (g : x.right ⟶ V) (hg : Φ.right = g ≫ h) :
    (finiteEtaleBaseChangeFactor B S hS Φ h g hg).left ≫ pullback.fst a.hom h = Φ.left :=
  FiniteEtaleCovers.baseChangeLift_comp_fst B S hS a h Φ.left (x.hom ≫ g) _

/-- The factorisation of `Φ` followed by the second projection is `x.hom ≫ g`. -/
@[simp]
lemma finiteEtaleBaseChangeFactor_left_comp_snd {x a : FiniteEtaleCovers B S hS} (Φ : x ⟶ a)
    {V : BigFppfOver B S hS} (h : V ⟶ a.right) (g : x.right ⟶ V) (hg : Φ.right = g ≫ h) :
    (finiteEtaleBaseChangeFactor B S hS Φ h g hg).left ≫ pullback.snd a.hom h = x.hom ≫ g :=
  FiniteEtaleCovers.baseChangeLift_comp_snd B S hS a h Φ.left (x.hom ≫ g) _

/-- The factorisation of `Φ` through a base change of its target recovers `Φ`. -/
lemma finiteEtaleBaseChangeFactor_comp {x a : FiniteEtaleCovers B S hS} (Φ : x ⟶ a)
    {V : BigFppfOver B S hS} (h : V ⟶ a.right) (g : x.right ⟶ V) (hg : Φ.right = g ≫ h) :
    finiteEtaleBaseChangeFactor B S hS Φ h g hg ≫ FiniteEtaleCovers.baseChangeHom B S hS a h = Φ :=
  MorphismProperty.Arrow.Hom.ext
    (FiniteEtaleCovers.baseChangeLift_comp_fst B S hS a h Φ.left (x.hom ≫ g) _) hg.symm

/-- The section of the base change of `a` along `k ≫ a.hom` attached to a morphism
`k : V ⟶ a.left` into the total space of `a`: its two projections are `k` and the identity. -/
noncomputable def finiteEtaleBaseChangeSection (a : FiniteEtaleCovers B S hS)
    {V : BigFppfOver B S hS} (k : V ⟶ a.left) :
    V ⟶ (FiniteEtaleCovers.baseChange B S hS a (k ≫ a.hom)).left :=
  FiniteEtaleCovers.baseChangeLift B S hS a (k ≫ a.hom) k (𝟙 V) (Category.id_comp _).symm

/-- The section attached to `k` followed by the first projection is `k`. -/
@[simp]
lemma finiteEtaleBaseChangeSection_comp_fst (a : FiniteEtaleCovers B S hS)
    {V : BigFppfOver B S hS} (k : V ⟶ a.left) :
    finiteEtaleBaseChangeSection B S hS a k ≫ pullback.fst a.hom (k ≫ a.hom) = k :=
  FiniteEtaleCovers.baseChangeLift_comp_fst B S hS a (k ≫ a.hom) k (𝟙 V) _

/-- The section attached to `k` followed by the second projection is the identity. -/
@[simp]
lemma finiteEtaleBaseChangeSection_comp_snd (a : FiniteEtaleCovers B S hS)
    {V : BigFppfOver B S hS} (k : V ⟶ a.left) :
    finiteEtaleBaseChangeSection B S hS a k ≫ pullback.snd a.hom (k ≫ a.hom) = 𝟙 V :=
  FiniteEtaleCovers.baseChangeLift_comp_snd B S hS a (k ≫ a.hom) k (𝟙 V) _

/-- The section attached to `g ≫ k` followed by the comparison between the base changes
along `(g ≫ k) ≫ a.hom` and along `k ≫ a.hom` is `g` followed by the section attached
to `k`. -/
lemma finiteEtaleBaseChangeSection_comp_factor (a : FiniteEtaleCovers B S hS)
    {V V' : BigFppfOver B S hS} (k : V ⟶ a.left) (g : V' ⟶ V) :
    finiteEtaleBaseChangeSection B S hS a (g ≫ k) ≫
        (finiteEtaleBaseChangeFactor B S hS
          (FiniteEtaleCovers.baseChangeHom B S hS a ((g ≫ k) ≫ a.hom)) (k ≫ a.hom) g
          (Category.assoc g k a.hom)).left =
      g ≫ finiteEtaleBaseChangeSection B S hS a k := by
  refine finiteEtaleBaseChange_left_hom_ext B S hS a (k ≫ a.hom) ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => finiteEtaleBaseChangeSection B S hS a (g ≫ k) ≫ m)
      (finiteEtaleBaseChangeFactor_left_comp_fst B S hS
        (FiniteEtaleCovers.baseChangeHom B S hS a ((g ≫ k) ≫ a.hom)) (k ≫ a.hom) g
        (Category.assoc g k a.hom))).trans ?_
    refine (finiteEtaleBaseChangeSection_comp_fst B S hS a (g ≫ k)).trans ?_
    refine (congrArg (fun m => g ≫ m)
      (finiteEtaleBaseChangeSection_comp_fst B S hS a k)).symm.trans ?_
    exact (Category.assoc _ _ _).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => finiteEtaleBaseChangeSection B S hS a (g ≫ k) ≫ m)
      (finiteEtaleBaseChangeFactor_left_comp_snd B S hS
        (FiniteEtaleCovers.baseChangeHom B S hS a ((g ≫ k) ≫ a.hom)) (k ≫ a.hom) g
        (Category.assoc g k a.hom))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun m => m ≫ g)
      (finiteEtaleBaseChangeSection_comp_snd B S hS a (g ≫ k))).trans ?_
    refine (Category.id_comp g).trans ?_
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun m => g ≫ m)
        (finiteEtaleBaseChangeSection_comp_snd B S hS a k)).trans (Category.comp_id g))).symm

/-- The section attached to the left leg of a morphism `Φ` of `FÉt`, followed by the
comparison between the base changes along `Φ.left ≫ a.hom` and along `Φ.right`, is the left
leg of the factorisation of `Φ` through the base change of its target along `Φ.right`. -/
lemma finiteEtaleBaseChangeSection_comp_factor_left {x a : FiniteEtaleCovers B S hS}
    (Φ : x ⟶ a) :
    finiteEtaleBaseChangeSection B S hS a Φ.left ≫
        (finiteEtaleBaseChangeFactor B S hS
          (FiniteEtaleCovers.baseChangeHom B S hS a (Φ.left ≫ a.hom)) Φ.right x.hom
          (MorphismProperty.Arrow.w Φ)).left =
      (finiteEtaleBaseChangeFactor B S hS Φ Φ.right (𝟙 x.right)
        (Category.id_comp Φ.right).symm).left := by
  refine finiteEtaleBaseChange_left_hom_ext B S hS a Φ.right ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => finiteEtaleBaseChangeSection B S hS a Φ.left ≫ m)
      (finiteEtaleBaseChangeFactor_left_comp_fst B S hS
        (FiniteEtaleCovers.baseChangeHom B S hS a (Φ.left ≫ a.hom)) Φ.right x.hom
        (MorphismProperty.Arrow.w Φ))).trans ?_
    refine (finiteEtaleBaseChangeSection_comp_fst B S hS a Φ.left).trans ?_
    exact (finiteEtaleBaseChangeFactor_left_comp_fst B S hS Φ Φ.right (𝟙 x.right)
      (Category.id_comp Φ.right).symm).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => finiteEtaleBaseChangeSection B S hS a Φ.left ≫ m)
      (finiteEtaleBaseChangeFactor_left_comp_snd B S hS
        (FiniteEtaleCovers.baseChangeHom B S hS a (Φ.left ≫ a.hom)) Φ.right x.hom
        (MorphismProperty.Arrow.w Φ))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun m => m ≫ x.hom)
      (finiteEtaleBaseChangeSection_comp_snd B S hS a Φ.left)).trans ?_
    refine (Category.id_comp x.hom).trans ?_
    exact ((finiteEtaleBaseChangeFactor_left_comp_snd B S hS Φ Φ.right (𝟙 x.right)
      (Category.id_comp Φ.right).symm).trans (Category.comp_id x.hom)).symm

/-! ### The gluing half of condition (2) of Stacks 026F -/

-- `FiniteEtaleCovers.baseChange` is a plain `def`, so a goal composing a morphism into the total
-- space of a base change with a projection of the fibre product is not type-correct at
-- `implicit` transparency and `rw` refuses it.
attribute [local implicit_reducible] FiniteEtaleCovers.baseChange MorphismProperty.Arrow.mk in
/-- **The gluing half of condition (2) of Stacks 026F for `FÉt`.** Let `a` and `b` be finite
étale covers, let `u` be a morphism of their bases and let `R` be a covering sieve of the base
of `a`. A family of morphisms `W ⟶ b` of `FÉt`, one for each morphism `W ⟶ a` lying over a
member of `R`, each lying over `u` and compatible with composition, comes from a morphism
`a ⟶ b` lying over `u`. -/
theorem finiteEtaleProjection_exists_glue {a b : FiniteEtaleCovers B S hS}
    (u : a.right ⟶ b.right) {R : Sieve a.right}
    (hRmem : R ∈ BigFppfOver.topology B S hS a.right)
    (F : ∀ {w : FiniteEtaleCovers B S hS} (Φ : w ⟶ a), R.arrows Φ.right → (w ⟶ b))
    (hFbase : ∀ {w : FiniteEtaleCovers B S hS} (Φ : w ⟶ a) (hΦ : R.arrows Φ.right),
      (F Φ hΦ).right = Φ.right ≫ u)
    (hFcomp : ∀ {w w' : FiniteEtaleCovers B S hS} (Ψ : w' ⟶ w) (Φ : w ⟶ a)
      (hΦ : R.arrows Φ.right) (hΨΦ : R.arrows (Ψ ≫ Φ).right),
      F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ) :
    ∃ G : a ⟶ b, G.right = u ∧
      ∀ {w : FiniteEtaleCovers B S hS} (Φ : w ⟶ a) (hΦ : R.arrows Φ.right),
        Φ ≫ G = F Φ hΦ := by
  have hRpb : Sieve.pullback a.hom R ∈ BigFppfOver.topology B S hS a.left :=
    (BigFppfOver.topology B S hS).pullback_stable _ hRmem
  -- `F` depends on the membership proof through proof irrelevance only.
  have hFcongr : ∀ {w : FiniteEtaleCovers B S hS} {Φ Φ' : w ⟶ a}, Φ = Φ' →
      ∀ (hΦ : R.arrows Φ.right) (hΦ' : R.arrows Φ'.right), F Φ hΦ = F Φ' hΦ' := by
    intro w Φ Φ' e hΦ hΦ'
    subst e
    rfl
  -- `F` at a morphism over `R` factors through `F` at the base change of its target.
  have hFfac : ∀ {x : FiniteEtaleCovers B S hS} (Φ : x ⟶ a) {V : BigFppfOver B S hS}
      (h : V ⟶ a.right) (g : x.right ⟶ V) (hg : Φ.right = g ≫ h) (hΦ : R.arrows Φ.right)
      (hh : R.arrows h), F Φ hΦ = finiteEtaleBaseChangeFactor B S hS Φ h g hg ≫
        F (FiniteEtaleCovers.baseChangeHom B S hS a h) hh := by
    intro x Φ V h g hg hΦ hh
    have hmem : R.arrows
        ((finiteEtaleBaseChangeFactor B S hS Φ h g hg ≫
          FiniteEtaleCovers.baseChangeHom B S hS a h).right) := R.downward_closed hh g
    refine (hFcongr (finiteEtaleBaseChangeFactor_comp B S hS Φ h g hg).symm hΦ hmem).trans
      (hFcomp _ _ hh hmem)
  -- The left leg of the glued morphism, obtained from the sheaf `yoneda.obj b.left`.
  obtain ⟨Gl, hGl⟩ : ∃ Gl : a.left ⟶ b.left, ∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ a.left)
      (hk : R.arrows (k ≫ a.hom)),
      k ≫ Gl = finiteEtaleBaseChangeSection B S hS a k ≫
        (F (FiniteEtaleCovers.baseChangeHom B S hS a (k ≫ a.hom)) hk).left := by
    have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
      (BigFppfOver.isSheaf_yoneda_obj B S hS b.left)
    have hcompat : Presieve.FamilyOfElements.Compatible
        (P := yoneda.obj b.left)
        (R := ((Sieve.pullback a.hom R : Sieve a.left) : Presieve a.left))
        (fun _ k hk => finiteEtaleBaseChangeSection B S hS a k ≫
          (F (FiniteEtaleCovers.baseChangeHom B S hS a (k ≫ a.hom)) hk).left) := by
      refine (Presieve.compatible_iff_sieveCompatible _).2 ?_
      intro V V' k g hk
      have hk' : R.arrows (k ≫ a.hom) := hk
      have hgk : R.arrows
          ((FiniteEtaleCovers.baseChangeHom B S hS a ((g ≫ k) ≫ a.hom)).right) :=
        (Sieve.pullback a.hom R).downward_closed hk g
      have hF := hFfac _ (k ≫ a.hom) g (Category.assoc g k a.hom) hgk hk'
      have hsec := finiteEtaleBaseChangeSection_comp_factor B S hS a k g
      show finiteEtaleBaseChangeSection B S hS a (g ≫ k) ≫
          (F (FiniteEtaleCovers.baseChangeHom B S hS a ((g ≫ k) ≫ a.hom)) hgk).left =
        g ≫ finiteEtaleBaseChangeSection B S hS a k ≫
          (F (FiniteEtaleCovers.baseChangeHom B S hS a (k ≫ a.hom)) hk').left
      rw [hF, MorphismProperty.Comma.comp_left, ← Category.assoc, hsec, Category.assoc]
    refine ⟨(hsh _ hRpb).amalgamate _ hcompat, ?_⟩
    intro V k hk
    exact (hsh _ hRpb).isAmalgamation hcompat k hk
  -- The glued morphism lies over `u`: this is the commuting square making it a morphism.
  have hsq : Gl ≫ b.hom = a.hom ≫ u := by
    have hshr := (isSheaf_iff_isSheaf_of_type _ _).1
      (BigFppfOver.isSheaf_yoneda_obj B S hS b.right)
    refine ((hshr _ hRpb).isSeparatedFor).ext ?_
    intro V k hk
    have hk' : R.arrows (k ≫ a.hom) := hk
    have hw := (MorphismProperty.Arrow.w
        (F (FiniteEtaleCovers.baseChangeHom B S hS a (k ≫ a.hom)) hk')).trans
      (congrArg (fun m => (FiniteEtaleCovers.baseChange B S hS a (k ≫ a.hom)).hom ≫ m)
        (hFbase (FiniteEtaleCovers.baseChangeHom B S hS a (k ≫ a.hom)) hk'))
    show k ≫ Gl ≫ b.hom = k ≫ a.hom ≫ u
    rw [← Category.assoc, hGl k hk', Category.assoc, hw, finiteEtaleBaseChange_hom,
      FiniteEtaleCovers.baseChangeHom_right, ← Category.assoc,
      finiteEtaleBaseChangeSection_comp_snd, Category.id_comp, Category.assoc]
  refine ⟨MorphismProperty.Arrow.homMk Gl u hsq, rfl, ?_⟩
  intro w Φ hΦ
  refine MorphismProperty.Arrow.Hom.ext ?_ (hFbase Φ hΦ).symm
  have hΦl : R.arrows (Φ.left ≫ a.hom) := by
    rw [MorphismProperty.Arrow.w Φ]
    exact R.downward_closed hΦ w.hom
  have hF := hFfac (FiniteEtaleCovers.baseChangeHom B S hS a (Φ.left ≫ a.hom)) Φ.right w.hom
    (MorphismProperty.Arrow.w Φ) hΦl hΦ
  have hF' := hFfac Φ Φ.right (𝟙 w.right) (Category.id_comp Φ.right).symm hΦ hΦ
  have hsec := finiteEtaleBaseChangeSection_comp_factor_left B S hS Φ
  show Φ.left ≫ Gl = (F Φ hΦ).left
  rw [hGl Φ.left hΦl, hF, hF', MorphismProperty.Comma.comp_left,
    MorphismProperty.Comma.comp_left, ← Category.assoc, hsec]

/-! ### Condition (2) of Stacks 026F for `FÉt` -/

/-- **Condition (2) of Stacks 026F for `FÉt`.** The presheaves `Mor(x, y)` of Stacks 02ZB
attached to two finite étale covers of one and the same base are sheaves for the fppf
topology: locally equal morphisms of `FÉt` are equal, and morphisms of `FÉt` given
compatibly over a covering sieve of the base glue. -/
@[stacks 0BLZ "condition (2) of Stacks 026F: the presheaves Mor(x, y) are fppf sheaves, so
  locally equal morphisms of `FÉt` are equal and morphisms given compatibly over a covering
  sieve glue. Condition (1) is `AlgebraicGeometry.finiteEtaleProjection_isFibered`."]
theorem finiteEtaleProjection_isMorSheaf (U : BigFppfOver B S hS)
    (x y : (finiteEtaleProjection B S hS).Fiber U) :
    Functor.IsMorSheaf (finiteEtaleProjection B S hS) (BigFppfOver.topology B S hS) U x y := by
  refine Functor.isMorSheaf_of_locallyEqual_of_amalgamation
    (fun h ↦ finiteEtaleProjection_eq_of_locallyEqual B S hS h) ?_ U x y
  intro a b u R hRmem F hFbase hFcomp
  exact finiteEtaleProjection_exists_glue B S hS u hRmem F hFbase hFcomp

end AlgebraicGeometry

end
