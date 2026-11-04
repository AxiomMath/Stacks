module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullyFaithful

/-!
# The pairwise condition of a descent datum as naturality across the members of a family

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces étale over `X`.  A morphism of the canonical descent data of Stacks 04W5 of two
`𝒪_X`-modules `M`, `N` is a family of morphisms `w i : (f i)^*M ⟶ (f i)^*N` subject to the
pairwise condition on the fibre products `Y i ×_X Y j`.  Along an étale morphism the inverse
image is restriction of sections, by Stacks 03LW, so each `w i` becomes a morphism
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm` of the étale restrictions, acting on
sections of `M` over the charts of `X` of the form `V ≫ f i`.

The result of this file is that the pairwise condition says exactly that this action is natural
in *arbitrary* morphisms of such charts, including morphisms that pass from a chart of one member
of the family to a chart of another:
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_naturality`.  That is the form in which a
morphism of descent data becomes a morphism of the two modules read on the charts of `X` that
come from the family.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect₂Inv` inverts the reading of a section
  of an iterated inverse image over a twice composed chart.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.PairChartData` bundles the geometry of a chart of
  `Y i ×_X Y j` that factors a given morphism of charts of `X`: the chart itself, its comparisons
  with the two given charts, the invertibility of the first of them, the identification of the
  two charts of `X` it induces, and the factorization.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_val_app_restrict`: the étale form of a
  morphism of inverse images commutes, on sections, with restriction along a morphism of charts
  of the source.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_compat_pair`: **the pairwise condition
  read on a chart of the fibre product** — over a chart `Z` of `Y i ×_X Y j` the two étale forms
  agree, once the two charts of `X` that `Z` induces are identified.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.nonempty_pairChartData`: a morphism of the charts
  of `X` induced by a chart of `Y i` and a chart of `Y j` is factored by a chart of `Y i ×_X Y j`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_naturality`: **the pairwise condition as
  naturality across the members of the family.**

## Implementation notes

Three shapes of the elaborator are worked around, and the arrangement of the file is what avoids
them.

The chart of `Y i ×_X Y j` attached to a morphism of charts of `X`, namely
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairChart`, carries the universal morphism into a
fibre product of presheaves together with two proofs of étaleness obtained by cancellation;
naming it in a statement makes the elaborator rebuild all of that, and that does not terminate.
This is why `AlgebraicGeometry.Space.QuasiCoherentDescent.PairChartData` exists: every statement
below mentions only a variable of that structure and its fields, the chart appears only inside
the proof of `AlgebraicGeometry.Space.QuasiCoherentDescent.nonempty_pairChartData`, and a
consumer obtains an inhabitant of the structure rather than the chart.  For the same reason the
pairwise condition is first read at an *arbitrary* chart of the fibre product, where nothing has
to be rebuilt, and only afterwards instantiated.

The proof that transfers the pairwise condition along the factoring chart is written as a chain
of equalities between terms whose types are stated explicitly, rather than as a sequence of
rewrites of the goal.  A rewrite of this goal produces a term which is type-correct only at the
default transparency — the small étale site of an algebraic space and the underlying category of
its ringed site are two descriptions of one category — and the next `isDefEq` against such a term
does not terminate.

The identification of the two charts of `X` that a chart of the fibre product induces is carried
by the structure as a *morphism* together with the two ways it inverts the transport of sections,
rather than as an equality of charts.  The reason is that this equality holds in two
definitionally equal shapes, at the composite morphisms `pairFst ≫ f i` and `pairSnd ≫ f j` and
at the iterated postcompositions, and the two consumers of it need different ones; a rewrite
cannot see through the difference, whereas the structure's morphism is a variable and matches
either.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {C D : AlgebraicSpaces B S hS}

/-! ### Restriction along an invertible morphism of charts -/

/-- Restricting a section along an invertible morphism of charts and back leaves it
unchanged. -/
theorem val_map_inv_val_map (A : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS A.1 A.2)
    {U₁ U₂ : SmallEtale B S hS A.1} (c : U₁ ⟶ U₂) [IsIso c] (t : M.val.obj (.op U₂)) :
    M.val.map (inv c).op (M.val.map c.op t) = t := by
  rw [val_map_comp, IsIso.inv_hom_id]
  simp only [op_id]
  exact CategoryTheory.congr_fun (M.val.map_id (.op U₂)) t

/-- Restriction of sections along an invertible morphism of charts is injective. -/
theorem val_map_injective_of_isIso (A : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS A.1 A.2) {U₁ U₂ : SmallEtale B S hS A.1} (c : U₁ ⟶ U₂)
    [IsIso c] {t t' : M.val.obj (.op U₂)}
    (h : M.val.map c.op t = M.val.map c.op t') : t = t' :=
  ((val_map_inv_val_map B S hS A M c t).symm.trans
      (congrArg (fun z => M.val.map (inv c).op z) h)).trans
    (val_map_inv_val_map B S hS A M c t')

/-- Restriction of a section along two equal morphisms of charts agrees. -/
theorem val_map_congr_of_eq (A : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS A.1 A.2)
    {U₁ U₂ : SmallEtale B S hS A.1} {c c' : U₁ ⟶ U₂} (h : c = c')
    (t : M.val.obj (.op U₂)) :
    M.val.map c.op t = M.val.map c'.op t := by
  rw [h]

/-! ### Restriction of sections of an étale restriction -/

/-- Restricting a section of the étale restriction of a module along a morphism of charts of the
source is restricting it along the induced morphism of charts of the target. -/
theorem etaleModulePullback_val_map_apply (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) {U U' : SmallEtale B S hS D.1} (c : U' ⟶ U)
    (t : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj U))) :
    ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.map c.op t =
      M.val.map ((smallEtalePostcomp B S hS g hg).map c).op t :=
  rfl

/-- The étale form of a morphism of inverse images commutes, on sections, with restriction along
a morphism of charts of the source. -/
theorem etaleForm_val_app_restrict (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    {M N : Modules.{u, u} B S hS C.1 C.2}
    (w : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    {U U' : SmallEtale B S hS D.1} (c : U' ⟶ U)
    (t : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj U))) :
    (etaleForm B S hS g hg w).val.app (.op U')
        (M.val.map ((smallEtalePostcomp B S hS g hg).map c).op t) =
      N.val.map ((smallEtalePostcomp B S hS g hg).map c).op
        ((etaleForm B S hS g hg w).val.app (.op U) t) := by
  rw [← etaleModulePullback_val_map_apply B S hS g hg M c t,
    ← etaleModulePullback_val_map_apply B S hS g hg N c
      ((etaleForm B S hS g hg w).val.app (.op U) t)]
  exact val_app_restrict B S hS (etaleForm B S hS g hg w) c t

/-! ### Inverting the reading of a section of an iterated inverse image -/

/-- The reading of a section of an iterated inverse image along two étale morphisms, over the
twice composed chart, inverted. -/
def etaleSect₂Inv {P Q A : AlgebraicSpaces B S hS} (c : P ⟶ Q) (hc : IsEtale B S hS c.hom)
    (g : Q ⟶ A) (hg : IsEtale B S hS g.hom) (M : Modules.{u, u} B S hS A.1 A.2)
    (U : SmallEtale B S hS P.1)
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj
      ((smallEtalePostcomp B S hS c hc).obj U)))) :
    ((modulePullback B S hS c).obj ((modulePullback B S hS g).obj M)).val.obj (.op U) :=
  etaleSectInv B S hS c hc ((modulePullback B S hS g).obj M) U
    (etaleSectInv B S hS g hg M ((smallEtalePostcomp B S hS c hc).obj U) s)

/-- Reading a section of an iterated inverse image back and reading it again is the identity. -/
theorem etaleSect₂_etaleSect₂Inv {P Q A : AlgebraicSpaces B S hS} (c : P ⟶ Q)
    (hc : IsEtale B S hS c.hom) (g : Q ⟶ A) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS A.1 A.2) (U : SmallEtale B S hS P.1)
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj
      ((smallEtalePostcomp B S hS c hc).obj U)))) :
    etaleSect₂ B S hS c hc g hg M U (etaleSect₂Inv B S hS c hc g hg M U s) = s :=
  (congrArg (etaleSect B S hS g hg M ((smallEtalePostcomp B S hS c hc).obj U))
      (etaleSect_etaleSectInv B S hS c hc ((modulePullback B S hS g).obj M) U
        (etaleSectInv B S hS g hg M ((smallEtalePostcomp B S hS c hc).obj U) s))).trans
    (etaleSect_etaleSectInv B S hS g hg M ((smallEtalePostcomp B S hS c hc).obj U) s)

variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### Transport of sections against restriction along an equality of charts -/

/-- Transport of sections along an equality of charts undoes restriction along it.  The two
proofs of the equality are independent arguments, so that the statement applies when the two
sides of the equality have been written in two definitionally equal ways. -/
theorem eqToHom_val_map_eqToHom_of_eq {V₁ V₂ : SmallEtale B S hS X.1} (p q : V₁ = V₂)
    (M : Modules.{u, u} B S hS X.1 X.2) (z : M.val.obj (.op V₂)) :
    eqToHom (congrArg (fun V : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op V)) q)
        (M.val.map (eqToHom p).op z) = z := by
  obtain rfl : p = q := rfl
  exact val_map_eqToHom_eqToHom B S hS p M z

/-- Restriction of sections along an equality of charts undoes the transport along it.  The two
proofs of the equality are independent arguments, as in
`AlgebraicGeometry.Space.QuasiCoherentDescent.eqToHom_val_map_eqToHom_of_eq`. -/
theorem val_map_eqToHom_eqToHom_of_eq {V₁ V₂ : SmallEtale B S hS X.1} (p q : V₁ = V₂)
    (M : Modules.{u, u} B S hS X.1 X.2) (t : M.val.obj (.op V₁)) :
    M.val.map (eqToHom p).op
        (eqToHom (congrArg (fun V : SmallEtale B S hS X.1 =>
          M.val.presheaf.obj (.op V)) q) t) = t := by
  obtain rfl : p = q := rfl
  exact eqToHom_val_map_eqToHom B S hS p M t

/-! ### The pairwise condition read on a chart of a pairwise fibre product -/

/-- The two charts of `X` obtained from a chart of the pairwise fibre product `Y i ×_X Y j` by
the two projections are equal: the two composites to `X` agree. -/
theorem postcomp_pairObj_eq {i j : I} (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    (smallEtalePostcomp B S hS (pairFst B S hS Yi f i j ≫ f i)
        (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))).obj Z =
      (smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j ≫ f j)
        (isEtale_comp B S hS (isEtale_pairSnd B S hS Yi f hf i j) (hf j))).obj Z :=
  smallEtalePostcomp_obj_congr B S hS
    (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))
    (isEtale_comp B S hS (isEtale_pairSnd B S hS Yi f hf i j) (hf j))
    (pair_condition B S hS Yi f i j) Z

/-- **The pairwise condition of a morphism of descent data, read on a chart of the pairwise fibre
product.**  Two morphisms of inverse images intertwined by the canonical comparison of
Stacks 04W5 have étale forms which agree on sections over a chart `Z` of `Y i ×_X Y j`, after the
two charts of `X` that `Z` induces are identified.

The chart `Z` is arbitrary; it is instantiated later at the chart produced by
`AlgebraicGeometry.Space.QuasiCoherentDescent.nonempty_pairChartData`. -/
theorem etaleForm_compat_pair (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    {M N : Modules.{u, u} B S hS X.1 X.2} {i j : I}
    (w₁ : (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (w₂ : (modulePullback B S hS (f j)).obj M ⟶ (modulePullback B S hS (f j)).obj N)
    (hw : ∀ (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
        (x : ((modulePullback B S hS (pairFst B S hS Yi f i j)).obj
          ((modulePullback B S hS (f i)).obj M)).val.obj (.op Z)),
      (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
            (pair_condition B S hS Yi f i j) N).hom.val.app (.op Z)
          (((modulePullback B S hS (pairFst B S hS Yi f i j)).map w₁).val.app (.op Z) x) =
        ((modulePullback B S hS (pairSnd B S hS Yi f i j)).map w₂).val.app (.op Z)
          ((canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
            (pair_condition B S hS Yi f i j) M).hom.val.app (.op Z) x))
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (t : M.val.obj (.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))) :
    eqToHom (congrArg (fun W : SmallEtale B S hS X.1 => N.val.presheaf.obj (.op W))
          (postcomp_pairObj_eq B S hS Yi f hf Z))
        ((etaleForm B S hS (f i) (hf i) w₁).val.app
          (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z)) t) =
      (etaleForm B S hS (f j) (hf j) w₂).val.app
        (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
        (eqToHom (congrArg (fun W : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op W))
          (postcomp_pairObj_eq B S hS Yi f hf Z)) t) := by
  obtain ⟨x, rfl⟩ : ∃ x, etaleSect₂ B S hS (pairFst B S hS Yi f i j)
      (isEtale_pairFst B S hS Yi f hf i j) (f i) (hf i) M Z x = t :=
    ⟨etaleSect₂Inv B S hS (pairFst B S hS Yi f i j) (isEtale_pairFst B S hS Yi f hf i j)
        (f i) (hf i) M Z t,
      etaleSect₂_etaleSect₂Inv B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j) (f i) (hf i) M Z t⟩
  convert etaleForm_compat_of_comparison B S hS (pairFst B S hS Yi f i j)
    (pairSnd B S hS Yi f i j) (f i) (f j) (pair_condition B S hS Yi f i j)
    (isEtale_pairFst B S hS Yi f hf i j) (isEtale_pairSnd B S hS Yi f hf i j) (hf i) (hf j)
    (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))
    (isEtale_comp B S hS (isEtale_pairSnd B S hS Yi f hf i j) (hf j))
    (hcomp.fst i j) (hcomp.snd i j) w₁ w₂ Z x
    (hw Z x)
    using 2

/-! ### The chart of a pairwise fibre product factoring a morphism of charts -/

/-- The geometry of a chart of the pairwise fibre product `Y i ×_X Y j` that factors a morphism
`k` of the charts of `X` induced by a chart `V` of `Y i` and a chart `V'` of `Y j`: the chart
itself, its two comparisons with `V` and `V'`, the invertibility of the first one, the
identification `mid` of the two charts of `X` that the chart induces, and the factorization of
`k` through them.

This is `AlgebraicGeometry.Space.QuasiCoherentDescent.pairChart` and its companions, bundled so
that no statement has to name them. -/
structure PairChartData {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') where
  /-- The chart of the pairwise fibre product. -/
  obj : SmallEtale B S hS (pair B S hS Yi f i j).1
  /-- Its comparison, through the first projection, with the given chart of `Y i`. -/
  fst : (smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
      (isEtale_pairFst B S hS Yi f hf i j)).obj obj ⟶ V
  /-- Its comparison, through the second projection, with the given chart of `Y j`. -/
  snd : (smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
      (isEtale_pairSnd B S hS Yi f hf i j)).obj obj ⟶ V'
  /-- The first comparison is invertible. -/
  isIso_fst : IsIso fst
  /-- The identification of the chart of `X` under the first projection with the one under the
  second projection. -/
  mid : (smallEtalePostcomp B S hS (f i) (hf i)).obj
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj obj) ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj obj)
  /-- The two comparisons factor `k` through the identification. -/
  postcomp_comp : (smallEtalePostcomp B S hS (f i) (hf i)).map fst ≫ k =
      mid ≫ (smallEtalePostcomp B S hS (f j) (hf j)).map snd
  /-- Transport along the equality of the two charts of `X` undoes restriction along `mid`. -/
  eqToHom_val_map_mid : ∀ (M : Modules.{u, u} B S hS X.1 X.2)
      (z : M.val.obj (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j ≫ f j)
        (isEtale_comp B S hS (isEtale_pairSnd B S hS Yi f hf i j) (hf j))).obj obj))),
    eqToHom (congrArg (fun W : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op W))
        (postcomp_pairObj_eq B S hS Yi f hf obj)) (M.val.map mid.op z) = z
  /-- Restriction along `mid` undoes the transport along the equality of the two charts. -/
  val_map_mid_eqToHom : ∀ (M : Modules.{u, u} B S hS X.1 X.2)
      (t : M.val.obj (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j ≫ f i)
        (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))).obj obj))),
    M.val.map mid.op (eqToHom (congrArg (fun W : SmallEtale B S hS X.1 =>
      M.val.presheaf.obj (.op W)) (postcomp_pairObj_eq B S hS Yi f hf obj)) t) = t

/-- **Every morphism of the charts of `X` induced by a chart of `Y i` and a chart of `Y j` is
factored by a chart of `Y i ×_X Y j`.**  The chart is
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairChart`; it is returned as an inhabitant of
`AlgebraicGeometry.Space.QuasiCoherentDescent.PairChartData` rather than as itself, so that a
consumer never names it. -/
theorem nonempty_pairChartData {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    Nonempty (PairChartData B S hS Yi f hf V V' k) :=
  ⟨{ obj := pairChart B S hS Yi f hf V V' k
     fst := pairChartFst B S hS Yi f hf V V' k
     snd := pairChartSnd B S hS Yi f hf V V' k
     isIso_fst := isIso_pairChartFst B S hS Yi f hf V V' k
     mid := eqToHom (postcomp_pairChart_eq B S hS Yi f hf V V' k)
     postcomp_comp := postcomp_pairChartFst_comp B S hS Yi f hf V V' k
     eqToHom_val_map_mid := fun M z =>
       eqToHom_val_map_eqToHom_of_eq B S hS _
         (postcomp_pairObj_eq B S hS Yi f hf (pairChart B S hS Yi f hf V V' k)) M z
     val_map_mid_eqToHom := fun M t =>
       val_map_eqToHom_eqToHom_of_eq B S hS _
         (postcomp_pairObj_eq B S hS Yi f hf (pairChart B S hS Yi f hf V V' k)) M t }⟩

/-! ### Naturality across the members of the family -/

/-- Restricting a section first along the morphism `k` of charts of `X` and then along the first
comparison of a factoring chart is restricting it along the second comparison and then along the
identification of the two induced charts. -/
theorem val_map_fst_comp_of_pairChartData (M : Modules.{u, u} B S hS X.1 X.2) {i j : I}
    {V : SmallEtale B S hS (Yi i).1} {V' : SmallEtale B S hS (Yi j).1}
    {k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V'}
    (cd : PairChartData B S hS Yi f hf V V' k)
    (t : M.val.obj (.op ((smallEtalePostcomp B S hS (f j) (hf j)).obj V'))) :
    M.val.map ((smallEtalePostcomp B S hS (f i) (hf i)).map cd.fst).op (M.val.map k.op t) =
      M.val.map cd.mid.op
        (M.val.map ((smallEtalePostcomp B S hS (f j) (hf j)).map cd.snd).op t) :=
  ((val_map_comp B S hS ((smallEtalePostcomp B S hS (f i) (hf i)).map cd.fst) k t).trans
      (val_map_congr_of_eq B S hS X M cd.postcomp_comp t)).trans
    (val_map_comp B S hS cd.mid ((smallEtalePostcomp B S hS (f j) (hf j)).map cd.snd) t).symm

/-- The étale form on the `i`-th member, read over the chart `V` and restricted along the first
comparison of a factoring chart, is that form read over the chart of `Y i` that the factoring
chart induces. -/
theorem etaleForm_restrict_fst_of_pairChartData
    {M N : Modules.{u, u} B S hS X.1 X.2} {i j : I}
    (w₁ : (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    {V : SmallEtale B S hS (Yi i).1} {V' : SmallEtale B S hS (Yi j).1}
    {k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V'}
    (cd : PairChartData B S hS Yi f hf V V' k)
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS (f j) (hf j)).obj V'))) :
    N.val.map ((smallEtalePostcomp B S hS (f i) (hf i)).map cd.fst).op
        ((etaleForm B S hS (f i) (hf i) w₁).val.app (.op V) (M.val.map k.op s)) =
      (etaleForm B S hS (f i) (hf i) w₁).val.app
        (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj cd.obj))
        (M.val.map cd.mid.op
          (M.val.map ((smallEtalePostcomp B S hS (f j) (hf j)).map cd.snd).op s)) :=
  (etaleForm_val_app_restrict B S hS (f i) (hf i) w₁ cd.fst
      (M.val.map k.op s)).symm.trans
    (congrArg (fun z => (etaleForm B S hS (f i) (hf i) w₁).val.app
        (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj cd.obj)) z)
      (val_map_fst_comp_of_pairChartData B S hS Yi f hf M cd s))

/-- The étale form on the `j`-th member, read over the chart of `Y j` that a factoring chart
induces and restricted along the identification of the two induced charts of `X`, is that form
read over the chart `V'` and restricted along `k` and the first comparison. -/
theorem etaleForm_restrict_snd_of_pairChartData
    {M N : Modules.{u, u} B S hS X.1 X.2} {i j : I}
    (w₂ : (modulePullback B S hS (f j)).obj M ⟶ (modulePullback B S hS (f j)).obj N)
    {V : SmallEtale B S hS (Yi i).1} {V' : SmallEtale B S hS (Yi j).1}
    {k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V'}
    (cd : PairChartData B S hS Yi f hf V V' k)
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS (f j) (hf j)).obj V'))) :
    N.val.map cd.mid.op ((etaleForm B S hS (f j) (hf j) w₂).val.app
        (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj cd.obj))
        (M.val.map ((smallEtalePostcomp B S hS (f j) (hf j)).map cd.snd).op s)) =
      N.val.map ((smallEtalePostcomp B S hS (f i) (hf i)).map cd.fst).op
        (N.val.map k.op ((etaleForm B S hS (f j) (hf j) w₂).val.app (.op V') s)) :=
  (congrArg (fun z => N.val.map cd.mid.op z)
      (etaleForm_val_app_restrict B S hS (f j) (hf j) w₂ cd.snd s)).trans
    (val_map_fst_comp_of_pairChartData B S hS Yi f hf N cd
      ((etaleForm B S hS (f j) (hf j) w₂).val.app (.op V') s)).symm

/-- **The pairwise condition read along the identification carried by a factoring chart.**  Over
the chart of the pairwise fibre product that
`AlgebraicGeometry.Space.QuasiCoherentDescent.PairChartData` provides, the two étale forms are
intertwined by restriction along the identification `mid` of the two induced charts of `X`. -/
theorem etaleForm_compat_of_pairChartData (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    {M N : Modules.{u, u} B S hS X.1 X.2} {i j : I}
    (w₁ : (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (w₂ : (modulePullback B S hS (f j)).obj M ⟶ (modulePullback B S hS (f j)).obj N)
    (hw : ∀ (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
        (x : ((modulePullback B S hS (pairFst B S hS Yi f i j)).obj
          ((modulePullback B S hS (f i)).obj M)).val.obj (.op Z)),
      (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
            (pair_condition B S hS Yi f i j) N).hom.val.app (.op Z)
          (((modulePullback B S hS (pairFst B S hS Yi f i j)).map w₁).val.app (.op Z) x) =
        ((modulePullback B S hS (pairSnd B S hS Yi f i j)).map w₂).val.app (.op Z)
          ((canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
            (pair_condition B S hS Yi f i j) M).hom.val.app (.op Z) x))
    {V : SmallEtale B S hS (Yi i).1} {V' : SmallEtale B S hS (Yi j).1}
    {k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V'}
    (cd : PairChartData B S hS Yi f hf V V' k)
    (u : M.val.obj (.op ((smallEtalePostcomp B S hS (f j) (hf j)).obj
      ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
        (isEtale_pairSnd B S hS Yi f hf i j)).obj cd.obj)))) :
    (etaleForm B S hS (f i) (hf i) w₁).val.app
        (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj cd.obj))
        (M.val.map cd.mid.op u) =
      N.val.map cd.mid.op ((etaleForm B S hS (f j) (hf j) w₂).val.app
        (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj cd.obj)) u) := by
  have h1 := etaleForm_compat_pair B S hS Yi f hf hcomp w₁ w₂ hw cd.obj
    (M.val.map cd.mid.op u)
  rw [cd.eqToHom_val_map_mid M u] at h1
  rw [← h1]
  exact (cd.val_map_mid_eqToHom N
    ((etaleForm B S hS (f i) (hf i) w₁).val.app
      (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj cd.obj))
      (M.val.map cd.mid.op u))).symm

/-- **The pairwise condition, transferred along a factoring chart of the fibre product.**  Given
the compatibility of the two étale forms along the identification that
`AlgebraicGeometry.Space.QuasiCoherentDescent.PairChartData` carries, they are intertwined by
restriction along the given morphism `k` of charts of `X`. -/
theorem etaleForm_naturality_of_pairChartData
    {M N : Modules.{u, u} B S hS X.1 X.2} {i j : I}
    (w₁ : (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (w₂ : (modulePullback B S hS (f j)).obj M ⟶ (modulePullback B S hS (f j)).obj N)
    {V : SmallEtale B S hS (Yi i).1} {V' : SmallEtale B S hS (Yi j).1}
    {k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V'}
    (cd : PairChartData B S hS Yi f hf V V' k)
    (hcompat : ∀ u : M.val.obj (.op ((smallEtalePostcomp B S hS (f j) (hf j)).obj
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj cd.obj))),
      (etaleForm B S hS (f i) (hf i) w₁).val.app
          (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj cd.obj))
          (M.val.map cd.mid.op u) =
        N.val.map cd.mid.op ((etaleForm B S hS (f j) (hf j) w₂).val.app
          (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj cd.obj)) u))
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS (f j) (hf j)).obj V'))) :
    (etaleForm B S hS (f i) (hf i) w₁).val.app (.op V) (M.val.map k.op s) =
      N.val.map k.op ((etaleForm B S hS (f j) (hf j) w₂).val.app (.op V') s) := by
  have := cd.isIso_fst
  refine val_map_injective_of_isIso B S hS X N
    ((smallEtalePostcomp B S hS (f i) (hf i)).map cd.fst) ?_
  exact (etaleForm_restrict_fst_of_pairChartData B S hS Yi f hf w₁ cd s).trans
    ((hcompat (M.val.map ((smallEtalePostcomp B S hS (f j) (hf j)).map cd.snd).op s)).trans
      (etaleForm_restrict_snd_of_pairChartData B S hS Yi f hf w₂ cd s))

/-- **The pairwise condition of a morphism of descent data is naturality across the members of
the family.**  Two morphisms of inverse images intertwined by the canonical comparison of
Stacks 04W5 on `Y i ×_X Y j` have étale forms which are intertwined by restriction along an
arbitrary morphism, in the small étale site of `X`, from a chart induced by `Y i` to a chart
induced by `Y j`.

This is what makes a morphism of canonical descent data a morphism of the two modules, read on
the charts of `X` coming from the family. -/
theorem etaleForm_naturality_of_sections (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    {M N : Modules.{u, u} B S hS X.1 X.2} {i j : I}
    (w₁ : (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (w₂ : (modulePullback B S hS (f j)).obj M ⟶ (modulePullback B S hS (f j)).obj N)
    (hw : ∀ (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
        (x : ((modulePullback B S hS (pairFst B S hS Yi f i j)).obj
          ((modulePullback B S hS (f i)).obj M)).val.obj (.op Z)),
      (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
            (pair_condition B S hS Yi f i j) N).hom.val.app (.op Z)
          (((modulePullback B S hS (pairFst B S hS Yi f i j)).map w₁).val.app (.op Z) x) =
        ((modulePullback B S hS (pairSnd B S hS Yi f i j)).map w₂).val.app (.op Z)
          ((canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
            (pair_condition B S hS Yi f i j) M).hom.val.app (.op Z) x))
    {V : SmallEtale B S hS (Yi i).1} {V' : SmallEtale B S hS (Yi j).1}
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V')
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS (f j) (hf j)).obj V'))) :
    (etaleForm B S hS (f i) (hf i) w₁).val.app (.op V) (M.val.map k.op s) =
      N.val.map k.op ((etaleForm B S hS (f j) (hf j) w₂).val.app (.op V') s) := by
  obtain ⟨cd⟩ := nonempty_pairChartData B S hS Yi f hf V V' k
  exact etaleForm_naturality_of_pairChartData B S hS Yi f hf w₁ w₂ cd
    (fun u => etaleForm_compat_of_pairChartData B S hS Yi f hf hcomp w₁ w₂ hw cd u) s

/-- **The pairwise condition of a morphism of descent data is naturality across the members of
the family**, with the pairwise condition given as an equation of morphisms.  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_naturality_of_sections` read through
`AlgebraicGeometry.Space.QuasiCoherentDescent.comparison_val_app_of_naturality`. -/
theorem etaleForm_naturality (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    {M N : Modules.{u, u} B S hS X.1 X.2} {i j : I}
    (w₁ : (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (w₂ : (modulePullback B S hS (f j)).obj M ⟶ (modulePullback B S hS (f j)).obj N)
    (hw : (modulePullback B S hS (pairFst B S hS Yi f i j)).map w₁ ≫
        (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
          (pair_condition B S hS Yi f i j) N).hom =
      (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
          (pair_condition B S hS Yi f i j) M).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi f i j)).map w₂)
    {V : SmallEtale B S hS (Yi i).1} {V' : SmallEtale B S hS (Yi j).1}
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V')
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS (f j) (hf j)).obj V'))) :
    (etaleForm B S hS (f i) (hf i) w₁).val.app (.op V) (M.val.map k.op s) =
      N.val.map k.op ((etaleForm B S hS (f j) (hf j) w₂).val.app (.op V') s) :=
  etaleForm_naturality_of_sections B S hS Yi f hf hcomp w₁ w₂
    (fun Z x => comparison_val_app_of_naturality B S hS (pairFst B S hS Yi f i j)
      (pairSnd B S hS Yi f i j) (f i) (f j) (pair_condition B S hS Yi f i j) w₁ w₂ hw Z x) k s

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
