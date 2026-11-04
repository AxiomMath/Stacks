module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormCalculus
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.EquationDivision
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.GlobalResidueSequence
public import StacksFrontier.RingTheory.DeRham.MapExteriorPowerNaturality

/-!
# Forms vanishing on a divisor, locally, in terms of a local equation

Let `f : X ⟶ S` be a morphism of schemes, `Y ⊆ X` the closed subscheme cut out by `I`, and `t`
the local equation of `Y` on an open `U` attached to a trivialization of its ideal sheaf
(`Stacks.Divisors.IdealTrivialization`).

* A local relative `(p + 1)`-form restricting to zero on `Y` is, near every point, of the form
  `t α + dt ∧ β`; a local function vanishing on `Y` is, near every point, a multiple of `t`.
* If the de Rham complex of log poles is defined ([Stacks, Tag 0FMV]), a relation
  `t α + dt ∧ β = 0` forces `β` to restrict to zero on `Y`.

These are the two local inputs of the construction of the de Rham complex of log poles in
[Stacks, Tag 0FMW]; both are proved at the stalks, from their ring-theoretic counterparts
`Stacks.LogPoles.ker_mapExteriorPower_quotient_succ` and
`Stacks.LogPoles.mapExteriorPower_snd_eq_zero_of_mem_logRel`.

The passage to the stalks rests on one compatibility, proved here: under the identification
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv` of the stalk of
`Ω^p_{X/S}` at `x` with `⋀^p Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`, wedging a local form with an exact one-form
`dc` becomes `exteriorPower.wedgeLeft (D c_x)` on germs.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsStalkKaehlerEquiv_germ_exactWedge`:
  the germ of `dc ∧ β` is `D(c_x) ∧ β_x`, read in `⋀^{p+1} Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`.
* `Stacks.Divisors.IdealTrivialization.exists_local_eq_smul_add_exactWedge`: a `(p + 1)`-form
  vanishing on `Y` is locally `t α + dt ∧ β`.
* `Stacks.Divisors.IdealTrivialization.exists_local_eq_smul`: a function vanishing on `Y` is
  locally a multiple of `t`.
* `Stacks.Divisors.IdealTrivialization.formRestriction_eq_zero_of_smul_add_exactWedge_eq_zero`:
  under the condition of Tag 0FMV, `t α + dt ∧ β = 0` implies `β|_Y = 0`.

## Implementation notes

The compatibility of the stalk identification with `dc ∧ -` is checked on multiples of exact
wedges `d b₁ ∧ ⋯ ∧ d b_p`, which generate `Ω^p_{X/S}` locally
(`AlgebraicGeometry.SheafOfModules.exteriorPower_induction`); on those, `dc ∧ d b₁ ∧ ⋯ ∧ d b_p`
is again an ordered product of exact one-forms, whose germ is computed by
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv_germ`.

At a point of `Y` the ring-theoretic statements are about `𝒪_{X,x} ⧸ (t)`, while the stalk of the
restriction of forms is about `𝒪_{Y,x}`; the two have the same kernel of restriction of forms
because they are isomorphic `𝒪_{X,x}`-algebras
(`KaehlerDifferential.ker_mapExteriorPower_eq_of_algEquiv`). At a point off `Y` the germ of `t`
is a unit and the statements are immediate.

## References

* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

/-! ### Wedging with an exact one-form, on ordered products and at the stalks -/

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A term transported along an equality of degrees is heterogeneously equal to itself. -/
private theorem heq_degCast {V : ℤ → Type u} {a b : ℤ} (h : a = b) (x : V a) :
    HEq (Stacks.degCast (F := V) h x) x := by
  subst h; rfl

/-- **`dc ∧ (s₁ ∧ ⋯ ∧ s_p)` is the ordered product `dc ∧ s₁ ∧ ⋯ ∧ s_p`** of degree-one local
sections of `Ω^•_{X/S}`, for local sections `s_j` of `Ω_{X/S}`. -/
theorem exactWedge_homogeneousProd (p : ℕ) (V : X.Opens) (c : Γ(X, V))
    (s : Fin p → (relativeDifferentials f).val.obj (op V)) :
    exactWedge f p V c
        ((relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProd (op V) p
          fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app (op V)
            (s j)) =
      (relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProd (op V) (p + 1)
          fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app (op V)
            ((Fin.cons ((universalRelativeDerivation f).d c) s :
              Fin (p + 1) → (relativeDifferentials f).val.obj (op V)) j) := by
  have h1 := Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd
    (relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra (op V) p
      fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app (op V) (s j)
  have h2 := Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd
    (relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra (op V) (p + 1)
      fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app (op V)
        ((Fin.cons ((universalRelativeDerivation f).d c) s :
          Fin (p + 1) → (relativeDifferentials f).val.obj (op V)) j)
  rw [← h1, ← h2]
  refine eq_of_heq ((AlgebraicGeometry.SheafOfModules.reindexForm_heq _ _ _ _).trans ?_)
  refine HEq.trans ?_ (heq_degCast _ _).symm
  exact HEq.rfl

/-- `dc ∧ d b₁ ∧ ⋯ ∧ d b_p` is the exact wedge of the family `(c, b₁, …, b_p)`. -/
theorem exactWedge_homogeneousProd_d (p : ℕ) (V : X.Opens) (c : Γ(X, V))
    (b : Fin p → Γ(X, V)) :
    exactWedge f p V c
        ((relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProd (op V) p
          fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app (op V)
            ((universalRelativeDerivation f).d (b j))) =
      (relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProd (op V) (p + 1)
          fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app (op V)
            ((universalRelativeDerivation f).d ((Fin.cons c b : Fin (p + 1) → Γ(X, V)) j)) := by
  refine (exactWedge_homogeneousProd f p V c _).trans (congrArg _ (funext fun j => ?_))
  exact Fin.cases rfl (fun _ => rfl) j

/-- **An exact wedge is an ordered product of exact one-forms**: a local section of `Ω^p_{X/S}`
satisfying `AlgebraicGeometry.SheafOfModules.IsExactWedge` is `d b₁ ∧ ⋯ ∧ d b_p` for local
functions `b_j`, written with `Stacks.GradedAlgebra.homogeneousProd`. -/
theorem exists_eq_homogeneousProd_of_isExactWedge (U : X.Opensᵒᵖ) :
    ∀ (p : ℕ) (ω : ((deRhamAlgebras f).exteriorPower p).val.obj U),
      AlgebraicGeometry.SheafOfModules.IsExactWedge (deRhamAlgebras f) U p ω →
      ∃ b : Fin p → Γ(X, U.unop), ω =
        (relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProd U p
          fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U
            ((universalRelativeDerivation f).d (b j))
  | 0, ω, hω => ⟨Fin.elim0, hω⟩
  | p + 1, ω, hω => by
      obtain ⟨a, η, hη, he⟩ := hω
      obtain ⟨b, rfl⟩ := exists_eq_homogeneousProd_of_isExactWedge U p η hη
      refine ⟨Fin.cons a b, eq_of_heq (he.trans ?_)⟩
      refine HEq.trans
        (AlgebraicGeometry.SheafOfModules.reindexForm_heq _ (Nat.add_comm 1 p) _ _).symm ?_
      exact heq_of_eq (exactWedge_homogeneousProd_d f p U.unop a b)

section Stalk

open Stacks.RelativeDifferentialStalkMap

variable (x : X) [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- The identification of the stalk of `Ω^p_{X/S}` with `⋀^p Ω[𝒪_{X,x}⁄𝒪_{S,f x}]` is
semilinear on germs: the germ of `r ω` goes to the germ of `r` times the image of the germ of
`ω`. -/
theorem relativeDifferentialFormsStalkKaehlerEquiv_germ_smul (p : ℕ) (V : X.Opens)
    (hx : x ∈ V) (r : Γ(X, V)) (ω : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    letI := moduleStalkRelativeDifferentialForms f x p
    letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
      (f.stalkMap x).hom.toAlgebra
    relativeDifferentialFormsStalkKaehlerEquiv f x p
        (((relativeDifferentialForms f (p : ℤ)).presheaf.germ V x hx).hom (r • ω)) =
      (X.presheaf.germ V x hx).hom r •
        relativeDifferentialFormsStalkKaehlerEquiv f x p
          (((relativeDifferentialForms f (p : ℤ)).presheaf.germ V x hx).hom ω) := by
  let := moduleStalkRelativeDifferentialForms f x p
  let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  exact (congrArg (relativeDifferentialFormsStalkKaehlerEquiv f x p)
    (PresheafOfModules.germ_smul (R := X.presheaf) (relativeDifferentialForms f (p : ℤ)).val
      x V hx r ω)).trans (map_smul _ _ _)

/-- The germ of `dc ∧ d b₁ ∧ ⋯ ∧ d b_p` goes to `D(c_x) ∧` the image of the germ of
`d b₁ ∧ ⋯ ∧ d b_p`. -/
theorem relativeDifferentialFormsStalkKaehlerEquiv_germ_exactWedge_homogeneousProd (p : ℕ)
    (V : X.Opens) (hx : x ∈ V) (c : Γ(X, V)) (b : Fin p → Γ(X, V)) :
    letI := moduleStalkRelativeDifferentialForms f x p
    letI := moduleStalkRelativeDifferentialForms f x (p + 1)
    letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
      (f.stalkMap x).hom.toAlgebra
    relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
        (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ V x hx).hom
          (exactWedge f p V c
            ((relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProd (op V) p
              fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app (op V)
                ((universalRelativeDerivation f).d (b j))))) =
      exteriorPower.wedgeLeft (KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
          (ToType (X.presheaf.stalk x)) ((X.presheaf.germ V x hx).hom c)) p
        (relativeDifferentialFormsStalkKaehlerEquiv f x p
          (((relativeDifferentialForms f (p : ℤ)).presheaf.germ V x hx).hom
            ((relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProd (op V) p
              fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app (op V)
                ((universalRelativeDerivation f).d (b j))))) := by
  let := moduleStalkRelativeDifferentialForms f x p
  let := moduleStalkRelativeDifferentialForms f x (p + 1)
  let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  refine (congrArg (fun z => relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
    (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ V x hx).hom z))
    (exactWedge_homogeneousProd_d f p V c b)).trans ?_
  refine (relativeDifferentialFormsStalkKaehlerEquiv_germ f x (p + 1) V hx
    (Fin.cons c b)).trans ?_
  refine Eq.trans ?_ (congrArg _ (relativeDifferentialFormsStalkKaehlerEquiv_germ f x p V hx
    b)).symm
  refine Eq.trans ?_ (exteriorPower.wedgeLeft_ιMulti _ _ _).symm
  exact congrArg _ (funext fun j => Fin.cases rfl (fun _ => rfl) j)

/-- **Wedging with an exact one-form, at the stalk.** Under the identification of the stalk at
`x` of `Ω^•_{X/S}` with `⋀ Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`, the germ of `dc ∧ ω` is `D(c_x) ∧ ω_x`.

Both sides are additive in `ω`, semilinear, and compatible with restriction, so it suffices to
treat multiples of exact wedges, which generate `Ω^p_{X/S}` locally. -/
theorem relativeDifferentialFormsStalkKaehlerEquiv_germ_exactWedge (p : ℕ)
    (V : X.Opens) (hx : x ∈ V) (c : Γ(X, V)) (ω : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    letI := moduleStalkRelativeDifferentialForms f x p
    letI := moduleStalkRelativeDifferentialForms f x (p + 1)
    letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
      (f.stalkMap x).hom.toAlgebra
    relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
        (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ V x hx).hom
          (exactWedge f p V c ω)) =
      exteriorPower.wedgeLeft (KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
          (ToType (X.presheaf.stalk x)) ((X.presheaf.germ V x hx).hom c)) p
        (relativeDifferentialFormsStalkKaehlerEquiv f x p
          (((relativeDifferentialForms f (p : ℤ)).presheaf.germ V x hx).hom ω)) := by
  let := moduleStalkRelativeDifferentialForms f x p
  let := moduleStalkRelativeDifferentialForms f x (p + 1)
  let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  refine AlgebraicGeometry.SheafOfModules.exteriorPower_induction (deRhamAlgebras f) p
    (fun U ξ => ∀ (hxU : x ∈ U.unop) (c : Γ(X, U.unop)),
      relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
        (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ U.unop x hxU).hom
          (exactWedge f p U.unop c ξ)) =
      exteriorPower.wedgeLeft (KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
          (ToType (X.presheaf.stalk x)) ((X.presheaf.germ U.unop x hxU).hom c)) p
        (relativeDifferentialFormsStalkKaehlerEquiv f x p
          (((relativeDifferentialForms f (p : ℤ)).presheaf.germ U.unop x hxU).hom ξ)))
    ?_ ?_ ?_ ?_ ?_ (op V) ω hx c
  · intro U hxU c
    refine (congrArg (fun z => relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
        (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ U.unop x hxU).hom z))
      (exactWedge_zero_right p U.unop c)).trans ?_
    refine (congrArg (relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1))
      ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ U.unop x
        hxU).hom.map_zero).trans ?_
    refine ((relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)).map_zero).trans ?_
    refine Eq.symm ((congrArg (fun z => exteriorPower.wedgeLeft (KaehlerDifferential.D
        (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))
          ((X.presheaf.germ U.unop x hxU).hom c)) p
        (relativeDifferentialFormsStalkKaehlerEquiv f x p z))
      ((relativeDifferentialForms f (p : ℤ)).presheaf.germ U.unop x hxU).hom.map_zero).trans ?_)
    refine (congrArg (exteriorPower.wedgeLeft (KaehlerDifferential.D
        (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))
          ((X.presheaf.germ U.unop x hxU).hom c)) p)
        (relativeDifferentialFormsStalkKaehlerEquiv f x p).map_zero).trans ?_
    exact map_zero _
  · intro U ξ η hξ hη hxU c
    refine (congrArg (fun z => relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
        (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ U.unop x hxU).hom z))
      (exactWedge_add_right p U.unop c ξ η)).trans ?_
    refine (congrArg (relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1))
      (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ U.unop x
        hxU).hom.map_add _ _)).trans ?_
    refine ((relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)).map_add _ _).trans ?_
    refine (congrArg₂ (· + ·) (hξ hxU c) (hη hxU c)).trans ?_
    refine Eq.symm ((congrArg (fun z => exteriorPower.wedgeLeft (KaehlerDifferential.D
        (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))
          ((X.presheaf.germ U.unop x hxU).hom c)) p
        (relativeDifferentialFormsStalkKaehlerEquiv f x p z))
      (((relativeDifferentialForms f (p : ℤ)).presheaf.germ U.unop x
        hxU).hom.map_add ξ η)).trans ?_)
    refine (congrArg (exteriorPower.wedgeLeft (KaehlerDifferential.D
        (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))
          ((X.presheaf.germ U.unop x hxU).hom c)) p)
        ((relativeDifferentialFormsStalkKaehlerEquiv f x p).map_add _ _)).trans ?_
    exact map_add _ _ _
  · intro U ξ hξ hxU c
    refine (congrArg (fun z => relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
        (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ U.unop x hxU).hom z))
      (exactWedge_neg_right p U.unop c ξ)).trans ?_
    refine (congrArg (relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1))
      (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ U.unop x
        hxU).hom.map_neg _)).trans ?_
    refine ((relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)).map_neg _).trans ?_
    refine (congrArg (fun z => -z) (hξ hxU c)).trans ?_
    refine Eq.symm ((congrArg (fun z => exteriorPower.wedgeLeft (KaehlerDifferential.D
        (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))
          ((X.presheaf.germ U.unop x hxU).hom c)) p
        (relativeDifferentialFormsStalkKaehlerEquiv f x p z))
      (((relativeDifferentialForms f (p : ℤ)).presheaf.germ U.unop x
        hxU).hom.map_neg ξ)).trans ?_)
    refine (congrArg (exteriorPower.wedgeLeft (KaehlerDifferential.D
        (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))
          ((X.presheaf.germ U.unop x hxU).hom c)) p)
        ((relativeDifferentialFormsStalkKaehlerEquiv f x p).map_neg _)).trans ?_
    exact map_neg _ _
  · intro U ξ Sv hSv hall hxU c
    obtain ⟨V', g, hg, hxV'⟩ := hSv x hxU
    have h := hall V' g hg hxV' (X.presheaf.map (homOfLE g.le).op c)
    have e₁ : ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ V' x hxV').hom
        (exactWedge f p V' (X.presheaf.map (homOfLE g.le).op c)
          ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE g.le).op ξ)) =
        ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ U.unop x hxU).hom
          (exactWedge f p U.unop c ξ) :=
      (congrArg ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ V' x hxV').hom
        (exactWedge_res p g.le c ξ)).symm.trans
        ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ_res_apply (homOfLE g.le)
          x hxV' _)
    have e₂ : (X.presheaf.germ V' x hxV').hom (X.presheaf.map (homOfLE g.le).op c) =
        (X.presheaf.germ U.unop x hxU).hom c :=
      X.presheaf.germ_res_apply (homOfLE g.le) x hxV' c
    have e₃ : ((relativeDifferentialForms f (p : ℤ)).presheaf.germ V' x hxV').hom
        ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE g.le).op ξ) =
        ((relativeDifferentialForms f (p : ℤ)).presheaf.germ U.unop x hxU).hom ξ :=
      (relativeDifferentialForms f (p : ℤ)).presheaf.germ_res_apply (homOfLE g.le) x hxV' ξ
    refine (congrArg (relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)) e₁).symm.trans
      (h.trans ?_)
    exact congrArg₂ (fun a b => exteriorPower.wedgeLeft (KaehlerDifferential.D
      (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) a) p
        (relativeDifferentialFormsStalkKaehlerEquiv f x p b)) e₂ e₃
  · intro U b η hη hxU c
    obtain ⟨b', rfl⟩ := exists_eq_homogeneousProd_of_isExactWedge f U p η hη
    have h₁ := exactWedge_smul_right (f := f) p U.unop b c
      ((relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProd U p
          fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U
            ((universalRelativeDerivation f).d (b' j)))
    refine (congrArg (fun z => relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
      (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ U.unop x hxU).hom z))
        h₁).trans ?_
    refine (relativeDifferentialFormsStalkKaehlerEquiv_germ_smul f x (p + 1) U.unop hxU b
      _).trans ?_
    refine (congrArg (fun z => (X.presheaf.germ U.unop x hxU).hom b • z)
      (relativeDifferentialFormsStalkKaehlerEquiv_germ_exactWedge_homogeneousProd f x p U.unop
        hxU c b')).trans ?_
    refine (map_smul _ _ _).symm.trans ?_
    exact congrArg (exteriorPower.wedgeLeft (KaehlerDifferential.D
        (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))
          ((X.presheaf.germ U.unop x hxU).hom c)) p)
      (relativeDifferentialFormsStalkKaehlerEquiv_germ_smul f x p U.unop hxU b _).symm

/-- The germ of `r α + dc ∧ β` goes to `r_x α_x + D(c_x) ∧ β_x`. -/
theorem relativeDifferentialFormsStalkKaehlerEquiv_germ_smul_add_exactWedge (p : ℕ)
    (V : X.Opens) (hx : x ∈ V) (r c : Γ(X, V))
    (α : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    letI := moduleStalkRelativeDifferentialForms f x p
    letI := moduleStalkRelativeDifferentialForms f x (p + 1)
    letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
      (f.stalkMap x).hom.toAlgebra
    relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
        (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ V x hx).hom
          (r • α + exactWedge f p V c β)) =
      (X.presheaf.germ V x hx).hom r • relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
          (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ V x hx).hom α) +
        exteriorPower.wedgeLeft (KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
          (ToType (X.presheaf.stalk x)) ((X.presheaf.germ V x hx).hom c)) p
        (relativeDifferentialFormsStalkKaehlerEquiv f x p
          (((relativeDifferentialForms f (p : ℤ)).presheaf.germ V x hx).hom β)) := by
  let := moduleStalkRelativeDifferentialForms f x p
  let := moduleStalkRelativeDifferentialForms f x (p + 1)
  let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  refine (congrArg (relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1))
    (((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ V x
      hx).hom.map_add _ _)).trans ?_
  refine ((relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)).map_add _ _).trans ?_
  exact congrArg₂ (· + ·)
    (relativeDifferentialFormsStalkKaehlerEquiv_germ_smul f x (p + 1) V hx r α)
    (relativeDifferentialFormsStalkKaehlerEquiv_germ_exactWedge f x p V hx c β)

/-- **Every element of `⋀^n Ω[𝒪_{X,x}⁄𝒪_{S,f x}]` is the image of the germ of a local
`n`-form**, defined on a neighbourhood of `x` inside any given one. -/
theorem exists_relativeDifferentialFormsStalkKaehlerEquiv_germ_eq (n : ℕ) (V : X.Opens)
    (hx : x ∈ V)
    (ζ : letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
        (f.stalkMap x).hom.toAlgebra
      ⋀[ToType (X.presheaf.stalk x)]^n
        (KaehlerDifferential (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)))) :
    ∃ (V' : X.Opens) (_hV' : V' ≤ V) (hx' : x ∈ V')
      (ω : Γ(relativeDifferentialForms f (n : ℤ), V')),
      letI := moduleStalkRelativeDifferentialForms f x n
      letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
        (f.stalkMap x).hom.toAlgebra
      relativeDifferentialFormsStalkKaehlerEquiv f x n
        (((relativeDifferentialForms f (n : ℤ)).presheaf.germ V' x hx').hom ω) = ζ := by
  let := moduleStalkRelativeDifferentialForms f x n
  let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  obtain ⟨V₁, hx₁, s, hs⟩ := (relativeDifferentialForms f (n : ℤ)).presheaf.exists_germ_eq
    ((relativeDifferentialFormsStalkKaehlerEquiv f x n).symm ζ)
  refine ⟨V ⊓ V₁, inf_le_left, ⟨hx, hx₁⟩,
    (relativeDifferentialForms f (n : ℤ)).presheaf.map (homOfLE inf_le_right).op s, ?_⟩
  refine (congrArg (relativeDifferentialFormsStalkKaehlerEquiv f x n)
    (((relativeDifferentialForms f (n : ℤ)).presheaf.germ_res_apply (homOfLE inf_le_right) x
      ⟨hx, hx₁⟩ s).trans hs)).trans ?_
  exact (relativeDifferentialFormsStalkKaehlerEquiv f x n).apply_symm_apply ζ

end Stalk

/-- **A form vanishing on a closed subscheme has germ in the kernel of the restriction of
Kähler forms.** If `κ|_Y = 0` then at a point `y` of `Y` the image of the germ of `κ` in
`⋀^n Ω[𝒪_{X,y}⁄𝒪_{S,f y}]` restricts to zero in `⋀^n Ω[𝒪_{Y,y}⁄𝒪_{S,f y}]`. -/
theorem mapExteriorPower_germ_eq_zero_of_formRestriction_eq_zero (I : X.IdealSheafData)
    {W : X.Opens} (n : ℕ) (κ : Γ(relativeDifferentialForms f (n : ℤ), W))
    (hκ : (formRestriction I.subschemeι f (n : ℤ)).val.app (op W) κ = 0) (y : I.subscheme)
    (hy : I.subschemeι y ∈ W)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds (I.subschemeι y)))] :
    letI := Stacks.GysinStalk.algebraRestriction I.subschemeι y
    letI : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (X.presheaf.stalk (I.subschemeι y))) :=
      (f.stalkMap (I.subschemeι y)).hom.toAlgebra
    letI : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (I.subscheme.presheaf.stalk y)) := Stacks.GysinStalk.algebraSub I.subschemeι f y
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (X.presheaf.stalk (I.subschemeι y))) (ToType (I.subscheme.presheaf.stalk y)) :=
      Stacks.GysinStalk.isScalarTower_stalk_comp I.subschemeι f y
    letI := Stacks.RelativeDifferentialStalkMap.moduleStalkRelativeDifferentialForms f
      (I.subschemeι y) n
    KaehlerDifferential.mapExteriorPower (ToType (S.presheaf.stalk (f (I.subschemeι y))))
      (ToType (X.presheaf.stalk (I.subschemeι y))) (ToType (I.subscheme.presheaf.stalk y)) n
      (Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv f
        (I.subschemeι y) n
        (((relativeDifferentialForms f (n : ℤ)).presheaf.germ W (I.subschemeι y) hy).hom κ)) =
      0 := by
  classical
  let := Stacks.GysinStalk.algebraSub I.subschemeι f y
  refine (Stacks.GysinStalk.formsStalkMapEquation I.subschemeι f y n _).symm.trans ?_
  refine (congrArg (fun z =>
    Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (I.subschemeι ≫ f) y n
      (Stacks.Chow.stalkPushforwardComparison I.subschemeι
        (relativeDifferentialForms (I.subschemeι ≫ f) (n : ℤ)) y z))
    ((PresheafOfModules.stalkMapL_germ (R := X.sheaf.presheaf) (I.subschemeι y)
      (formRestriction I.subschemeι f (n : ℤ)).val W hy κ).trans
      ((congrArg _ hκ).trans (map_zero _)))).trans ?_
  exact (congrArg (Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (I.subschemeι ≫ f) y n) (Stacks.GysinStalk.stalkPushforwardComparison_zero
        I.subschemeι f y n)).trans (map_zero _)

end AlgebraicGeometry.Scheme.Hom

/-! ### Local generation of the forms vanishing on the divisor -/

namespace Stacks.Divisors.IdealTrivialization

open Stacks.RelativeDifferentialStalkMap

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- If `a b = 1` then `v = a (b v) + L 0` for any linear map `L`. -/
private theorem eq_smul_smul_add_map_zero_of_mul_eq_one {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (L : N →ₗ[R] M) {a b : R}
    (h : a * b = 1) (v : M) : v = a • (b • v) + L 0 := by
  rw [map_zero, add_zero, smul_smul, h, one_smul]

/-- If `a b = 1` then `v = a (b v)`. -/
private theorem eq_smul_smul_of_mul_eq_one {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {a b : R} (h : a * b = 1) (v : M) : v = a • (b • v) := by
  rw [smul_smul, h, one_smul]

/-- Restriction of forms to a ring `B ≅ A ⧸ (t)` kills `ξ` iff restriction to `A ⧸ (t)` does. -/
private theorem mapExteriorPower_eq_zero_iff_mem_ker_quotient {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    {t : A} (φ : (A ⧸ Ideal.span {t}) ≃ₐ[A] B) (n : ℕ) (ξ : ⋀[A]^n (KaehlerDifferential R A)) :
    KaehlerDifferential.mapExteriorPower R A B n ξ = 0 ↔
      ξ ∈ LinearMap.ker (KaehlerDifferential.mapExteriorPower R A (A ⧸ Ideal.span {t}) n) := by
  rw [KaehlerDifferential.ker_mapExteriorPower_eq_of_algEquiv R A φ n, LinearMap.mem_ker]

/-- The germ of the local equation at `x` is unchanged by restricting to a smaller open. -/
private theorem germ_equationAt_of_le {W W' : X.Opens} (hW : W ≤ U) (h : W' ≤ W) {x : X}
    (hx : x ∈ W) (hx' : x ∈ W') :
    (X.presheaf.germ W' x hx').hom (e.equationAt (h.trans hW)) =
      (X.presheaf.germ W x hx).hom (e.equationAt hW) :=
  (congrArg (X.presheaf.germ W' x hx').hom (e.equationAt_res hW h).symm).trans
    (X.presheaf.germ_res_apply (homOfLE h) x hx' _)

/-- The isomorphism `𝒪_{X,y} ⧸ (t) ≅ 𝒪_{Y,y}` of
`AlgebraicGeometry.Scheme.Hom.quotientSpanGermEquivStalk`, for the local equation `t`, as an
isomorphism of `𝒪_{X,y}`-algebras. -/
private def quotientSpanGermAlgEquivStalk {W : X.Opens} (hW : W ≤ U) (y : I.subscheme)
    (hy : I.subschemeι y ∈ W) :
    letI := Stacks.GysinStalk.algebraRestriction I.subschemeι y
    (ToType (X.presheaf.stalk (I.subschemeι y)) ⧸
        Ideal.span {(X.presheaf.germ W (I.subschemeι y) hy).hom (e.equationAt hW)}) ≃ₐ[
      ToType (X.presheaf.stalk (I.subschemeι y))] ToType (I.subscheme.presheaf.stalk y) :=
  letI := Stacks.GysinStalk.algebraRestriction I.subschemeι y
  AlgEquiv.ofRingEquiv (f := Scheme.Hom.quotientSpanGermEquivStalk y W hy (e.equationAt hW)
    (e.ker_stalkMap_eq_span_germ_equation hW y hy)) fun _ => rfl

/-- From the stalk to a neighbourhood, in positive degree: if the germ of `κ` at `x` is
`t_x ξ + D(t_x) ∧ ζ` in `⋀^{p+1} Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`, then near `x` the form `κ` is
`t α + dt ∧ β`. -/
theorem exists_local_eq_smul_add_exactWedge_of_stalk {W : X.Opens} (hW : W ≤ U) (p : ℕ)
    (κ : Γ(Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W)) (x : X) (hx : x ∈ W)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    (ξ : letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
        (f.stalkMap x).hom.toAlgebra
      ⋀[ToType (X.presheaf.stalk x)]^(p + 1)
        (KaehlerDifferential (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))))
    (ζ : letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
        (f.stalkMap x).hom.toAlgebra
      ⋀[ToType (X.presheaf.stalk x)]^p
        (KaehlerDifferential (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))))
    (h : letI := moduleStalkRelativeDifferentialForms f x (p + 1)
      letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
        (f.stalkMap x).hom.toAlgebra
      relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
        (((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ W x hx).hom
          κ) =
        (X.presheaf.germ W x hx).hom (e.equationAt hW) • ξ +
          exteriorPower.wedgeLeft (KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
            (ToType (X.presheaf.stalk x)) ((X.presheaf.germ W x hx).hom (e.equationAt hW))) p
            ζ) :
    ∃ (W' : X.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      ∃ (α : Γ(Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W'))
        (β : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), W')),
        (Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hW').op κ =
          e.equationAt (hW'.trans hW) • α +
            Scheme.Hom.exactWedge f p W' (e.equationAt (hW'.trans hW)) β := by
  let := moduleStalkRelativeDifferentialForms f x p
  let := moduleStalkRelativeDifferentialForms f x (p + 1)
  let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  obtain ⟨W₁, h₁, hx₁, α₁, hα₁⟩ :=
    Scheme.Hom.exists_relativeDifferentialFormsStalkKaehlerEquiv_germ_eq f x (p + 1) W hx ξ
  obtain ⟨W₂, h₂, hx₂, β₂, hβ₂⟩ :=
    Scheme.Hom.exists_relativeDifferentialFormsStalkKaehlerEquiv_germ_eq f x p W₁ hx₁ ζ
  have h₂W : W₂ ≤ W := h₂.trans h₁
  have hα₂ : relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)
      (((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ W₂ x hx₂).hom
        ((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map
          (homOfLE h₂).op α₁)) = ξ :=
    (congrArg (relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1))
      ((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ_res_apply
        (homOfLE h₂) x hx₂ α₁)).trans hα₁
  have ht := e.germ_equationAt_of_le hW h₂W hx hx₂
  have key : ((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ W x
      hx).hom κ =
      ((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ W₂ x hx₂).hom
        (e.equationAt (h₂W.trans hW) •
            (Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map
              (homOfLE h₂).op α₁ +
          Scheme.Hom.exactWedge f p W₂ (e.equationAt (h₂W.trans hW)) β₂) := by
    refine (relativeDifferentialFormsStalkKaehlerEquiv f x (p + 1)).injective (h.trans ?_)
    refine Eq.symm ((Scheme.Hom.relativeDifferentialFormsStalkKaehlerEquiv_germ_smul_add_exactWedge
      f x p W₂ hx₂ _ _ _ _).trans ?_)
    exact congrArg₂ (· + ·) (congrArg₂ (· • ·) ht hα₂)
      (congrArg₂ (fun a b => exteriorPower.wedgeLeft (KaehlerDifferential.D
        (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) a) p b) ht hβ₂)
  obtain ⟨W₃, hx₃, i₃, j₃, he⟩ :=
    (Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ_eq x hx hx₂ κ _ key
  refine ⟨W₃, leOfHom i₃, hx₃,
    (Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map j₃.op
      ((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map
        (homOfLE h₂).op α₁),
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map j₃.op β₂, he.trans ?_⟩
  rw [map_add, Scheme.Modules.map_smul]
  have h3 := Scheme.Hom.exactWedge_res (f := f) p (leOfHom j₃) (e.equationAt (h₂W.trans hW)) β₂
  have h4 := e.equationAt_res (h₂W.trans hW) (leOfHom j₃)
  exact congrArg₂ (· + ·) (congrArg (· • _) h4)
    (h3.trans (congrArg (fun c => Scheme.Hom.exactWedge f p W₃ c _) h4))

/-- From the stalk to a neighbourhood, by multiples of `t`: if the germ of `κ` at `x` is
`t_x ξ`, then near `x` the form `κ` is `t α`. -/
theorem exists_local_eq_smul_of_stalk {W : X.Opens} (hW : W ≤ U) (n : ℕ)
    (κ : Γ(Scheme.Hom.relativeDifferentialForms f (n : ℤ), W)) (x : X) (hx : x ∈ W)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    (ξ : letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
        (f.stalkMap x).hom.toAlgebra
      ⋀[ToType (X.presheaf.stalk x)]^n
        (KaehlerDifferential (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))))
    (h : letI := moduleStalkRelativeDifferentialForms f x n
      letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
        (f.stalkMap x).hom.toAlgebra
      relativeDifferentialFormsStalkKaehlerEquiv f x n
        (((Scheme.Hom.relativeDifferentialForms f (n : ℤ)).presheaf.germ W x hx).hom κ) =
        (X.presheaf.germ W x hx).hom (e.equationAt hW) • ξ) :
    ∃ (W' : X.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      ∃ α : Γ(Scheme.Hom.relativeDifferentialForms f (n : ℤ), W'),
        (Scheme.Hom.relativeDifferentialForms f (n : ℤ)).presheaf.map (homOfLE hW').op κ =
          e.equationAt (hW'.trans hW) • α := by
  let := moduleStalkRelativeDifferentialForms f x n
  let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  obtain ⟨W₁, h₁, hx₁, α₁, hα₁⟩ :=
    Scheme.Hom.exists_relativeDifferentialFormsStalkKaehlerEquiv_germ_eq f x n W hx ξ
  have ht := e.germ_equationAt_of_le hW h₁ hx hx₁
  have key : ((Scheme.Hom.relativeDifferentialForms f (n : ℤ)).presheaf.germ W x hx).hom κ =
      ((Scheme.Hom.relativeDifferentialForms f (n : ℤ)).presheaf.germ W₁ x hx₁).hom
        (e.equationAt (h₁.trans hW) • α₁) := by
    refine (relativeDifferentialFormsStalkKaehlerEquiv f x n).injective (h.trans ?_)
    refine Eq.symm ((Scheme.Hom.relativeDifferentialFormsStalkKaehlerEquiv_germ_smul
      f x n W₁ hx₁ _ _).trans ?_)
    exact congrArg₂ (· • ·) ht hα₁
  obtain ⟨W₃, hx₃, i₃, j₃, he⟩ :=
    (Scheme.Hom.relativeDifferentialForms f (n : ℤ)).presheaf.germ_eq x hx hx₁ κ _ key
  refine ⟨W₃, leOfHom i₃, hx₃,
    (Scheme.Hom.relativeDifferentialForms f (n : ℤ)).presheaf.map j₃.op α₁, he.trans ?_⟩
  rw [Scheme.Modules.map_smul]
  exact congrArg (· • _) (e.equationAt_res (h₁.trans hW) (leOfHom j₃))

/-- **Local generation of the forms vanishing on the divisor**, in positive degree: a local
`(p + 1)`-form restricting to zero on `Y` is near every point `t α + dt ∧ β`. -/
theorem exists_local_eq_smul_add_exactWedge {W : X.Opens} (hW : W ≤ U) (p : ℕ)
    (κ : Γ(Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (hκ : (Scheme.Hom.formRestriction I.subschemeι f ((p + 1 : ℕ) : ℤ)).val.app (op W) κ = 0)
    (x : X) (hx : x ∈ W) :
    ∃ (W' : X.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      ∃ (α : Γ(Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W'))
        (β : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), W')),
        (Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hW').op κ =
          e.equationAt (hW'.trans hW) • α +
            Scheme.Hom.exactWedge f p W' (e.equationAt (hW'.trans hW)) β := by
  classical
  by_cases hxY : x ∈ I.support
  · obtain ⟨y, rfl⟩ : x ∈ Set.range I.subschemeι := I.range_subschemeι.symm ▸ hxY
    let := Stacks.GysinStalk.algebraRestriction I.subschemeι y
    let : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (X.presheaf.stalk (I.subschemeι y))) :=
      (f.stalkMap (I.subschemeι y)).hom.toAlgebra
    let : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (I.subscheme.presheaf.stalk y)) := Stacks.GysinStalk.algebraSub I.subschemeι f y
    have : IsScalarTower (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (X.presheaf.stalk (I.subschemeι y))) (ToType (I.subscheme.presheaf.stalk y)) :=
      Stacks.GysinStalk.isScalarTower_stalk_comp I.subschemeι f y
    let := moduleStalkRelativeDifferentialForms f (I.subschemeι y) (p + 1)
    have hm := Scheme.Hom.mapExteriorPower_germ_eq_zero_of_formRestriction_eq_zero f I (p + 1)
      κ hκ y hx
    have hmem := ((mapExteriorPower_eq_zero_iff_mem_ker_quotient
      (e.quotientSpanGermAlgEquivStalk hW y hx) (p + 1) _).mp hm)
    rw [Stacks.LogPoles.ker_mapExteriorPower_quotient_succ,
      Stacks.LogPoles.logSubmodule_span_singleton] at hmem
    obtain ⟨a, ⟨ζ, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨ξ, rfl⟩ := Stacks.LogPoles.exists_smul_of_mem_span_singleton_smul_top _ hb
    exact e.exists_local_eq_smul_add_exactWedge_of_stalk hW p κ _ hx ξ ζ
      (hab.symm.trans (add_comm _ _))
  · let := moduleStalkRelativeDifferentialForms f x (p + 1)
    let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
      (f.stalkMap x).hom.toAlgebra
    obtain ⟨b, hb⟩ := (e.isUnit_germ_equation_of_not_mem hW x hx hxY).exists_right_inv
    exact e.exists_local_eq_smul_add_exactWedge_of_stalk hW p κ x hx _ 0
      (eq_smul_smul_add_map_zero_of_mul_eq_one _ hb _)

/-- **Local generation of the forms vanishing on the divisor**, in degree zero: a local
`0`-form restricting to zero on `Y` is near every point a multiple of `t`. -/
theorem exists_local_eq_smul {W : X.Opens} (hW : W ≤ U)
    (κ : Γ(Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ), W))
    (hκ : (Scheme.Hom.formRestriction I.subschemeι f ((0 : ℕ) : ℤ)).val.app (op W) κ = 0)
    (x : X) (hx : x ∈ W) :
    ∃ (W' : X.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      ∃ α : Γ(Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ), W'),
        (Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hW').op κ =
          e.equationAt (hW'.trans hW) • α := by
  classical
  by_cases hxY : x ∈ I.support
  · obtain ⟨y, rfl⟩ : x ∈ Set.range I.subschemeι := I.range_subschemeι.symm ▸ hxY
    let := Stacks.GysinStalk.algebraRestriction I.subschemeι y
    let : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (X.presheaf.stalk (I.subschemeι y))) :=
      (f.stalkMap (I.subschemeι y)).hom.toAlgebra
    let : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (I.subscheme.presheaf.stalk y)) := Stacks.GysinStalk.algebraSub I.subschemeι f y
    have : IsScalarTower (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (X.presheaf.stalk (I.subschemeι y))) (ToType (I.subscheme.presheaf.stalk y)) :=
      Stacks.GysinStalk.isScalarTower_stalk_comp I.subschemeι f y
    let := moduleStalkRelativeDifferentialForms f (I.subschemeι y) 0
    have hm := Scheme.Hom.mapExteriorPower_germ_eq_zero_of_formRestriction_eq_zero f I 0
      κ hκ y hx
    have hmem := ((mapExteriorPower_eq_zero_iff_mem_ker_quotient
      (e.quotientSpanGermAlgEquivStalk hW y hx) 0 _).mp hm)
    rw [Stacks.LogPoles.ker_mapExteriorPower_quotient_zero] at hmem
    obtain ⟨ξ, hξ⟩ := Stacks.LogPoles.exists_smul_of_mem_span_singleton_smul_top _ hmem
    exact e.exists_local_eq_smul_of_stalk hW 0 κ _ hx ξ hξ
  · let := moduleStalkRelativeDifferentialForms f x 0
    let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
      (f.stalkMap x).hom.toAlgebra
    obtain ⟨b, hb⟩ := (e.isUnit_germ_equation_of_not_mem hW x hx hxY).exists_right_inv
    exact e.exists_local_eq_smul_of_stalk hW 0 κ x hx _ (eq_smul_smul_of_mul_eq_one hb _)

/-- **A relation `t α + dt ∧ β = 0` forces `β` to vanish on the divisor**, when the de Rham
complex of log poles is defined. -/
theorem formRestriction_eq_zero_of_smul_add_exactWedge_eq_zero
    (h : f.HasLogPolesDeRhamComplex I) {W : X.Opens} (hW : W ≤ U) (p : ℕ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (β : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), W))
    (hαβ : e.equationAt hW • α + Scheme.Hom.exactWedge f p W (e.equationAt hW) β = 0) :
    (Scheme.Hom.formRestriction I.subschemeι f (p : ℤ)).val.app (op W) β = 0 := by
  classical
  refine TopCat.Presheaf.section_ext
    ⟨(Scheme.Hom.relativeDifferentialForms (I.subschemeι ≫ f) (p : ℤ)).presheaf,
      (Scheme.Hom.relativeDifferentialForms (I.subschemeι ≫ f) (p : ℤ)).isSheaf⟩
    (I.subschemeι ⁻¹ᵁ W) _ 0 fun y hy => ?_
  let := Stacks.GysinStalk.algebraRestriction I.subschemeι y
  let : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
      (ToType (X.presheaf.stalk (I.subschemeι y))) := (f.stalkMap (I.subschemeι y)).hom.toAlgebra
  let : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
      (ToType (I.subscheme.presheaf.stalk y)) := Stacks.GysinStalk.algebraSub I.subschemeι f y
  have : IsScalarTower (ToType (S.presheaf.stalk (f (I.subschemeι y))))
      (ToType (X.presheaf.stalk (I.subschemeι y))) (ToType (I.subscheme.presheaf.stalk y)) :=
    Stacks.GysinStalk.isScalarTower_stalk_comp I.subschemeι f y
  let := moduleStalkRelativeDifferentialForms f (I.subschemeι y) p
  let := moduleStalkRelativeDifferentialForms f (I.subschemeι y) (p + 1)
  have ht := e.ker_stalkMap_eq_span_germ_equation hW y hy
  have hrel : (relativeDifferentialFormsStalkKaehlerEquiv f (I.subschemeι y) (p + 1)
        (((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ W
          (I.subschemeι y) hy).hom α),
      relativeDifferentialFormsStalkKaehlerEquiv f (I.subschemeι y) p
        (((Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.germ W
          (I.subschemeι y) hy).hom β)) ∈
      Stacks.LogPoles.logRel (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        ((X.presheaf.germ W (I.subschemeι y) hy).hom (e.equationAt hW)) p := by
    refine (Stacks.LogPoles.mem_logRel_iff _ _ p).mpr ?_
    refine Eq.trans ?_ ((congrArg (fun z => relativeDifferentialFormsStalkKaehlerEquiv f
      (I.subschemeι y) (p + 1)
        (((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ W
          (I.subschemeι y) hy).hom z)) hαβ).trans ?_)
    · exact (Scheme.Hom.relativeDifferentialFormsStalkKaehlerEquiv_germ_smul_add_exactWedge f
        (I.subschemeι y) p W hy _ _ α β).symm
    · exact (congrArg (relativeDifferentialFormsStalkKaehlerEquiv f (I.subschemeι y) (p + 1))
        ((Scheme.Hom.relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.germ W
          (I.subschemeι y) hy).hom.map_zero).trans (map_zero _)
  have hq := Stacks.LogPoles.mapExteriorPower_snd_eq_zero_of_mem_logRel
    (Scheme.Hom.HasLogPolesDeRhamComplex.exists_retraction_D h y W hy _ ht) p hrel
  have hmap := (mapExteriorPower_eq_zero_iff_mem_ker_quotient
    (e.quotientSpanGermAlgEquivStalk hW y hy) p _).mpr hq
  let := Stacks.GysinStalk.algebraSub I.subschemeι f y
  refine (relativeDifferentialFormsStalkKaehlerEquiv (I.subschemeι ≫ f) y p).injective ?_
  refine Eq.trans ?_ ((congrArg (relativeDifferentialFormsStalkKaehlerEquiv (I.subschemeι ≫ f) y p)
    (map_zero _)).trans (map_zero _)).symm
  refine (congrArg (relativeDifferentialFormsStalkKaehlerEquiv (I.subschemeι ≫ f) y p)
    (Stacks.Chow.stalkPushforwardComparison_germ I.subschemeι
      (Scheme.Hom.relativeDifferentialForms (I.subschemeι ≫ f) (p : ℤ)) y W hy _).symm).trans ?_
  refine (congrArg (fun z => relativeDifferentialFormsStalkKaehlerEquiv (I.subschemeι ≫ f) y p
    (Stacks.Chow.stalkPushforwardComparison I.subschemeι
      (Scheme.Hom.relativeDifferentialForms (I.subschemeι ≫ f) (p : ℤ)) y z))
    (PresheafOfModules.stalkMapL_germ (R := X.sheaf.presheaf) (I.subschemeι y)
      (Scheme.Hom.formRestriction I.subschemeι f (p : ℤ)).val W hy β).symm).trans ?_
  exact (Stacks.GysinStalk.formsStalkMapEquation I.subschemeι f y p _).trans hmap

end Stacks.Divisors.IdealTrivialization

end
