module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCoveringFpqc
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.SolutionSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk
public import StacksFrontier.CategoryTheory.Sites.Point.FiniteTuples

/-!
# The geometric fibre of a solution sheaf is the solution set over the étale local ring

Let `S` be a scheme of a big étale site, let `s̄` be a geometric point of `S` and let
`P₁, …, P_n ∈ Γ(S, ⊤)[x₁, …, x_n]`.  The solutions of `P` form a presheaf
`Stacks.EtaleCohomology.solutionPresheaf` on the small étale site of `S`, whose sections over a
chart `U` are the tuples `a : Fin n → Γ(U, ⊤)` at which the `Pⱼ` vanish after their coefficients
are pushed along the structure map of `U`.  This file computes its **fibre at `s̄`**: it is the
set of solutions of `P` in the étale local ring `𝒪^{ét}_{S,s̄}`, with coefficients pushed along
the germ map `Γ(S, ⊤) ⟶ 𝒪^{ét}_{S,s̄}`.

Composed with `Stacks.EtaleCohomology.representableIsoSolutionPresheaf` — the identification of
the representable presheaf `h_V` of an affine chart with the solutions of a presentation of it —
and with `AlgebraicGeometry.yonedaCompEtaleStalkPresheafFunctorIso` — the stalk of a representable
presheaf as the fibre of the geometric point — it shows that the lifts of a geometric point to an
affine étale chart are the points of the chart with values in the étale local ring:
`AlgebraicGeometry.geometricPointFiberEquivEtaleLocalSolutions`. This is one of the
identifications in step (3) of the proof of [Stacks Project, Tag 04I6].

## Main definitions

* `AlgebraicGeometry.etaleLocalRingGerm` — the germ map `Γ(U, ⊤) ⟶ 𝒪^{ét}_{S,s̄}` at a chart `U`
  of `S` carrying a chosen lift of `s̄`.
* `AlgebraicGeometry.etaleCoefficientGerm` — the germ map `Γ(S, ⊤) ⟶ 𝒪^{ét}_{S,s̄}` on global
  functions, taken at the terminal chart.  This is the coefficient map along which the system `P`
  is pushed into the étale local ring.
* `AlgebraicGeometry.EtaleLocalSolutions` — the solutions of `P` in the étale local ring.
* `AlgebraicGeometry.geometricFiberSolutionsDesc` — the comparison map from the fibre of the
  solution presheaf to that solution set: a germ of a solution goes to the tuple of germs of its
  coordinates.

## Main results

* `AlgebraicGeometry.etaleLocalRingGerm_comp_schemeStructureHom` — the germ map at a chart,
  precomposed with the structure map of that chart, is `etaleCoefficientGerm`, independently of
  the chart and of the lift.  This is what makes the coefficient map of the limit system
  well defined.
* `AlgebraicGeometry.bijective_geometricFiberSolutionsDesc` and
  `AlgebraicGeometry.geometricFiberSolutionsEquiv` — **the computation**: the fibre at `s̄` of the
  presheaf of solutions of `P` is the set of solutions of `P` in the étale local ring at `s̄`.
* `AlgebraicGeometry.geometricPointFiberEquivEtaleLocalSolutions` — the same read on a
  representable: for an affine chart `V` of an affine `S` with a standard presentation `P`, the
  lifts of `s̄` to `V` are the solutions of `P` in `𝒪^{ét}_{S,s̄}`.

## Implementation notes

The étale local ring is the filtered colimit of the rings of global functions over the étale
neighbourhoods of `s̄` — that is its definition, `AlgebraicGeometry.etaleLocalRing` — and the
solution set of a system of polynomial equations in finitely many variables is a finite limit. So
the identification is an instance of filtered colimits commuting with finite limits, and it is
proved by the germ calculus of a point of a site for finite tuples:
`CategoryTheory.GrothendieckTopology.Point.exists_toPresheafFiber_tuple` gives surjectivity (a
tuple in the colimit comes from one neighbourhood, and the equations it satisfies there hold after
one restriction) and
`CategoryTheory.GrothendieckTopology.Point.exists_map_eq_of_toPresheafFiber_eq` gives injectivity.
In particular no use is made of the strict henselization as a limit of étale neighbourhoods, nor
of the limit arguments of [Stacks Project, Tag 01ZM].

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-! ### Germs of global functions on a chart -/

/-- **The germ map of the structure sheaf of the small étale site at a geometric point.**  A
global function on an étale chart `W` of `S`, together with a lift `w` of the geometric point
`s̄` to `W`, has a germ in the étale local ring at `s̄`.

This is the canonical map into the colimit defining
`AlgebraicGeometry.etaleLocalRing`, read as a ring homomorphism. -/
def etaleLocalRingGerm (W : SmallEtale B S hS) (w : (geometricPointFiber B S hS s).obj W) :
    Γ((SmallEtale.toScheme B S hS).obj W, ⊤) →+* ↥(etaleLocalRing B S hS s) :=
  ((geometricPointSitePoint B S hS s).toPresheafFiber W w
    (SmallEtale.structureSheaf B S hS).obj).hom

/-- The restriction maps of the structure sheaf of the small étale site are the ring maps on
global functions of the underlying morphisms of schemes.  This is the `RingCat`-valued form of
`AlgebraicGeometry.SmallEtale.commRingStructureSheaf_map`. -/
theorem SmallEtale.structureSheaf_map_eq_appTop {W W' : SmallEtale B S hS} (k : W' ⟶ W) :
    (SmallEtale.structureSheaf B S hS).obj.map k.op =
      RingCat.ofHom ((SmallEtale.toScheme B S hS).map k).appTop.hom :=
  rfl

/-- **Germs are unchanged by restriction.**  The germ at a chart `W'` of the restriction of a
global function on `W` along `k : W' ⟶ W` is the germ at `W` of that function, taken at the
image of the lift. -/
theorem etaleLocalRingGerm_map_appTop {W W' : SmallEtale B S hS} (k : W' ⟶ W)
    (w' : (geometricPointFiber B S hS s).obj W')
    (t : Γ((SmallEtale.toScheme B S hS).obj W, ⊤)) :
    etaleLocalRingGerm B S hS s W' w' (((SmallEtale.toScheme B S hS).map k).appTop.hom t) =
      etaleLocalRingGerm B S hS s W ((geometricPointFiber B S hS s).map k w') t :=
  (geometricPointSitePoint B S hS s).toPresheafFiber_w_apply k w'
    (SmallEtale.structureSheaf B S hS).obj t

/-- **The germ map on global functions of `S`**: the germ at the terminal chart `S / S`, whose
canonical lift of the geometric point is `AlgebraicGeometry.SmallEtale.finalLift`, precomposed
with the structure map of that chart.

This is the coefficient map along which a system of polynomial equations over `Γ(S, ⊤)` is pushed
into the étale local ring at `s̄`; by
`AlgebraicGeometry.etaleLocalRingGerm_comp_schemeStructureHom` it is also the germ map at *any*
chart precomposed with the structure map of that chart. -/
def etaleCoefficientGerm : Γ(S, ⊤) →+* ↥(etaleLocalRing B S hS s) :=
  (etaleLocalRingGerm B S hS s (SmallEtale.final B S hS)
      (SmallEtale.finalLift B S hS s)).comp
    (SmallEtale.schemeStructureHom B S hS (SmallEtale.final B S hS)).appTop.hom

/-- The germ map at a chart, precomposed with the structure map of that chart, does not depend on
the chart: a morphism of pointed étale neighbourhoods identifies the two composites, because
germs are unchanged by restriction and the structure maps are compatible. -/
theorem etaleLocalRingGerm_comp_schemeStructureHom_of_hom
    {E E' : (geometricPointFiber B S hS s).Elements} (f : E' ⟶ E) :
    (etaleLocalRingGerm B S hS s E.1 E.2).comp
        (SmallEtale.schemeStructureHom B S hS E.1).appTop.hom =
      (etaleLocalRingGerm B S hS s E'.1 E'.2).comp
        (SmallEtale.schemeStructureHom B S hS E'.1).appTop.hom := by
  refine RingHom.ext fun t => ?_
  have hres : (SmallEtale.schemeStructureHom B S hS E'.1).appTop.hom t =
      ((SmallEtale.toScheme B S hS).map f.1).appTop.hom
        ((SmallEtale.schemeStructureHom B S hS E.1).appTop.hom t) :=
    (congrArg (fun φ : Γ(S, ⊤) →+* Γ((SmallEtale.toScheme B S hS).obj E'.1, ⊤) => φ t)
      (appTop_schemeStructureHom_comp B S hS f.1)).symm
  rw [RingHom.comp_apply, RingHom.comp_apply, hres,
    etaleLocalRingGerm_map_appTop B S hS s f.1 E'.2,
    show (geometricPointFiber B S hS s).map f.1 E'.2 = E.2 from f.2]

/-- **The coefficient germ is the germ map at any chart.**  For every étale chart `W` of `S` and
every lift `w` of the geometric point to it, the germ map at `(W, w)` precomposed with the
structure map of `W` is `AlgebraicGeometry.etaleCoefficientGerm`.

The category of pointed étale neighbourhoods of a geometric point is cofiltered, so any two of
them are refined by a third, and
`AlgebraicGeometry.etaleLocalRingGerm_comp_schemeStructureHom_of_hom` identifies both composites
with the one at the refinement. -/
theorem etaleLocalRingGerm_comp_schemeStructureHom (W : SmallEtale B S hS)
    (w : (geometricPointFiber B S hS s).obj W) :
    (etaleLocalRingGerm B S hS s W w).comp
        (SmallEtale.schemeStructureHom B S hS W).appTop.hom =
      etaleCoefficientGerm B S hS s := by
  let e := Functor.elementsMk (geometricPointFiber B S hS s) W w
  let e' := Functor.elementsMk (geometricPointFiber B S hS s) (SmallEtale.final B S hS)
    (SmallEtale.finalLift B S hS s)
  exact (etaleLocalRingGerm_comp_schemeStructureHom_of_hom B S hS s
      (IsCofiltered.minToLeft e e')).trans
    (etaleLocalRingGerm_comp_schemeStructureHom_of_hom B S hS s
      (IsCofiltered.minToRight e e')).symm

/-! ### The fibre of the presheaf of solutions -/

section Solutions

variable {n : ℕ} (P : Fin n → MvPolynomial (Fin n) Γ(S, ⊤))

/-- **The solutions of a system of polynomial equations in the étale local ring.**  The
coefficients of the system, which live in the global functions on `S`, are pushed into the étale
local ring at `s̄` along `AlgebraicGeometry.etaleCoefficientGerm`. -/
abbrev EtaleLocalSolutions : Type u :=
  {a : Fin n → ↥(etaleLocalRing B S hS s) //
    MvPolynomial.IsSolution P (etaleCoefficientGerm B S hS s) a}

/-- **The germ of a solution.**  A solution of the system over a chart `W` carrying a lift of the
geometric point has a tuple of germs in the étale local ring, and that tuple is again a solution:
the germ map is a ring homomorphism, so it carries the vanishing of the pushed `Pⱼ` to the
vanishing of the `Pⱼ` pushed along the composite, and that composite is the coefficient germ by
`AlgebraicGeometry.etaleLocalRingGerm_comp_schemeStructureHom`. -/
def solutionGerm (W : SmallEtale B S hS) (w : (geometricPointFiber B S hS s).obj W) :
    Solutions B S hS P W → EtaleLocalSolutions B S hS s P :=
  fun a => ⟨fun i => etaleLocalRingGerm B S hS s W w (a.1 i), by
    have h := MvPolynomial.isSolution_comp (P := P)
      (SmallEtale.schemeStructureHom B S hS W).appTop.hom
      (etaleLocalRingGerm B S hS s W w) a.2
    rwa [etaleLocalRingGerm_comp_schemeStructureHom B S hS s W w] at h⟩

/-- The coordinates of the germ of a solution are the germs of its coordinates. -/
@[simp]
theorem solutionGerm_coe (W : SmallEtale B S hS)
    (w : (geometricPointFiber B S hS s).obj W) (a : Solutions B S hS P W) (i : Fin n) :
    (solutionGerm B S hS s P W w a).1 i = etaleLocalRingGerm B S hS s W w (a.1 i) :=
  rfl

/-- The germ of a solution, as a morphism of types out of the sections of the solution presheaf
over a pointed étale neighbourhood. -/
def solutionGermHom (W : SmallEtale B S hS) (w : (geometricPointFiber B S hS s).obj W) :
    (solutionPresheaf B S hS P).obj (op W) ⟶ EtaleLocalSolutions B S hS s P :=
  TypeCat.ofHom (solutionGerm B S hS s P W w)

/-- The germ of a solution is compatible with restriction, which is what lets the germ maps be
descended to the fibre of the solution presheaf. -/
theorem solutionGermHom_w {W W' : SmallEtale B S hS} (k : W' ⟶ W)
    (w' : (geometricPointFiber B S hS s).obj W') :
    (solutionPresheaf B S hS P).map k.op ≫ solutionGermHom B S hS s P W' w' =
      solutionGermHom B S hS s P W ((geometricPointFiber B S hS s).map k w') := by
  apply TypeCat.homEquiv.injective
  funext a
  simp only [TypeCat.homEquiv_apply, types_comp_apply]
  refine Subtype.ext (funext fun i => ?_)
  exact etaleLocalRingGerm_map_appTop B S hS s k w' (a.1 i)

/-- **The comparison map from the fibre of the solution presheaf to the solutions in the étale
local ring**, obtained by descending the germ maps of
`AlgebraicGeometry.solutionGerm` along the colimit defining the fibre. -/
def geometricFiberSolutionsDesc :
    (geometricPointSitePoint B S hS s).presheafFiber.obj (solutionPresheaf B S hS P) ⟶
      EtaleLocalSolutions B S hS s P :=
  (geometricPointSitePoint B S hS s).presheafFiberDesc
    (solutionGermHom B S hS s P)
    (fun {_ _} k w => solutionGermHom_w B S hS s P k w)

/-- The comparison map sends the germ in the fibre of a solution over a pointed étale
neighbourhood to the tuple of germs of its coordinates. -/
@[simp]
theorem geometricFiberSolutionsDesc_toPresheafFiber (W : SmallEtale B S hS)
    (w : (geometricPointFiber B S hS s).obj W) (a : Solutions B S hS P W) :
    geometricFiberSolutionsDesc B S hS s P
        ((geometricPointSitePoint B S hS s).toPresheafFiber W w
          (solutionPresheaf B S hS P) a) =
      solutionGerm B S hS s P W w a := by
  have h := ConcreteCategory.congr_hom
    ((geometricPointSitePoint B S hS s).toPresheafFiber_presheafFiberDesc
      (solutionGermHom B S hS s P)
      (fun {_ _} k w => solutionGermHom_w B S hS s P k w) W w) a
  exact h

private theorem eval_map_comp {R A A' : Type*} [CommRing R] [CommRing A] [CommRing A']
    (g : R →+* A) (ψ : A →+* A') {m : ℕ} (a : Fin m → A) (p : MvPolynomial (Fin m) R) :
    MvPolynomial.eval (fun i => ψ (a i)) (MvPolynomial.map (ψ.comp g) p) =
      ψ (MvPolynomial.eval a (MvPolynomial.map g p)) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left ψ g a p]
  rfl

/-- **The fibre at a geometric point of the presheaf of solutions of a system of polynomial
equations is the set of solutions of that system in the étale local ring.**

This is filtered colimits commuting with finite limits, run by hand.  *Surjectivity*: a tuple of
elements of the étale local ring comes from one étale neighbourhood
(`CategoryTheory.GrothendieckTopology.Point.exists_toPresheafFiber_tuple`), and the `n` equations
it satisfies in the colimit already hold after a single restriction
(`CategoryTheory.GrothendieckTopology.Point.exists_map_eq_of_toPresheafFiber_eq`), so it is the
germ of a genuine solution there.  *Injectivity*: two germs of solutions may be taken at a common
neighbourhood, and if their coordinatewise germs agree then the solutions agree after a single
restriction, by the same lemma. -/
theorem bijective_geometricFiberSolutionsDesc :
    Function.Bijective (geometricFiberSolutionsDesc B S hS s P) := by
  constructor
  · intro p₁ p₂ hp
    obtain ⟨Z, z, a₁, a₂, h₁, h₂⟩ :=
      (geometricPointSitePoint B S hS s).toPresheafFiber_jointly_surjective₂
        (P := solutionPresheaf B S hS P) p₁ p₂
    subst h₁
    subst h₂
    rw [geometricFiberSolutionsDesc_toPresheafFiber B S hS s P Z z a₁,
      geometricFiberSolutionsDesc_toPresheafFiber B S hS s P Z z a₂] at hp
    obtain ⟨Z', k, z', hz', hk⟩ :=
      (geometricPointSitePoint B S hS s).exists_map_eq_of_toPresheafFiber_eq
        (SmallEtale.structureSheaf B S hS).obj n Z z
        (show Solutions B S hS P Z from a₁).1 (show Solutions B S hS P Z from a₂).1
        (fun i => congrFun (congrArg Subtype.val hp) i)
    rw [← hz', ← (geometricPointSitePoint B S hS s).toPresheafFiber_w_apply k z'
        (solutionPresheaf B S hS P) a₁,
      ← (geometricPointSitePoint B S hS s).toPresheafFiber_w_apply k z'
        (solutionPresheaf B S hS P) a₂]
    exact congrArg _ (Subtype.ext (funext fun i => hk i))
  · intro c
    obtain ⟨Z, z, b₀, hb₀⟩ := (geometricPointSitePoint B S hS s).exists_toPresheafFiber_tuple
      (SmallEtale.structureSheaf B S hS).obj n c.1
    let b : Fin n → Γ((SmallEtale.toScheme B S hS).obj Z, ⊤) := b₀
    have hb : ∀ i, etaleLocalRingGerm B S hS s Z z (b i) = c.1 i := hb₀
    have hzero : ∀ j : Fin n, etaleLocalRingGerm B S hS s Z z
          (MvPolynomial.eval b (MvPolynomial.map
            (SmallEtale.schemeStructureHom B S hS Z).appTop.hom (P j))) =
        etaleLocalRingGerm B S hS s Z z 0 := by
      intro j
      have key := eval_map_comp (SmallEtale.schemeStructureHom B S hS Z).appTop.hom
        (etaleLocalRingGerm B S hS s Z z) b (P j)
      rw [etaleLocalRingGerm_comp_schemeStructureHom B S hS s Z z] at key
      rw [map_zero, ← key, show (fun i => etaleLocalRingGerm B S hS s Z z (b i)) = c.1
        from funext fun i => hb i]
      exact c.2 j
    obtain ⟨Z', k, z', hz', hk⟩ :=
      (geometricPointSitePoint B S hS s).exists_map_eq_of_toPresheafFiber_eq
        (SmallEtale.structureSheaf B S hS).obj n Z z
        (fun j => MvPolynomial.eval b (MvPolynomial.map
          (SmallEtale.schemeStructureHom B S hS Z).appTop.hom (P j)))
        (fun _ => 0) hzero
    have hk' : ∀ j : Fin n, ((SmallEtale.toScheme B S hS).map k).appTop.hom
        (MvPolynomial.eval b (MvPolynomial.map
          (SmallEtale.schemeStructureHom B S hS Z).appTop.hom (P j))) = 0 := fun j =>
      (show ((SmallEtale.toScheme B S hS).map k).appTop.hom
          (MvPolynomial.eval b (MvPolynomial.map
            (SmallEtale.schemeStructureHom B S hS Z).appTop.hom (P j))) =
        ((SmallEtale.toScheme B S hS).map k).appTop.hom 0 from hk j).trans (map_zero _)
    have hsol : MvPolynomial.IsSolution P
        (SmallEtale.schemeStructureHom B S hS Z').appTop.hom
        (fun i => ((SmallEtale.toScheme B S hS).map k).appTop.hom (b i)) := by
      intro j
      rw [← appTop_schemeStructureHom_comp B S hS k,
        eval_map_comp (SmallEtale.schemeStructureHom B S hS Z).appTop.hom
          ((SmallEtale.toScheme B S hS).map k).appTop.hom b (P j)]
      exact hk' j
    let a : Solutions B S hS P Z' :=
      ⟨fun i => ((SmallEtale.toScheme B S hS).map k).appTop.hom (b i), hsol⟩
    refine ⟨(geometricPointSitePoint B S hS s).toPresheafFiber Z' z'
      (solutionPresheaf B S hS P) (show (solutionPresheaf B S hS P).obj (op Z') from a), ?_⟩
    rw [geometricFiberSolutionsDesc_toPresheafFiber B S hS s P Z'
      (show (geometricPointFiber B S hS s).obj Z' from z') a]
    refine Subtype.ext (funext fun i => ?_)
    rw [solutionGerm_coe]
    refine (etaleLocalRingGerm_map_appTop B S hS s k
      (show (geometricPointFiber B S hS s).obj Z' from z') (b i)).trans ?_
    rw [show (geometricPointFiber B S hS s).map k
      (show (geometricPointFiber B S hS s).obj Z' from z') = z from hz']
    exact hb i

/-- **The fibre at a geometric point of the presheaf of solutions of a system of polynomial
equations is the solution set of that system in the étale local ring**, as a bijection. -/
def geometricFiberSolutionsEquiv :
    (geometricPointSitePoint B S hS s).presheafFiber.obj (solutionPresheaf B S hS P) ≃
      EtaleLocalSolutions B S hS s P :=
  Equiv.ofBijective _ (bijective_geometricFiberSolutionsDesc B S hS s P)

end Solutions

/-! ### The lifts of a geometric point to an affine chart -/

section Representable

variable [IsAffine S] {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(S, ⊤)}

/-- **The lifts of a geometric point to an étale chart are the points of the chart with values in
the étale local ring there.**  For an affine chart `V` of an affine scheme `S` with a standard
presentation `Γ(V, ⊤) = Γ(S, ⊤)[x₁, …, x_n]/(P₁, …, P_n)`, the set of lifts of a geometric point
`s̄` of `S` to `V` is the set of solutions of `P` in the étale local ring `𝒪^{ét}_{S,s̄}`.

It is
`AlgebraicGeometry.yonedaCompEtaleStalkPresheafFunctorIso` (the stalk of the representable
presheaf `h_V` is the set of lifts of `s̄`), followed by
`Stacks.EtaleCohomology.representableIsoSolutionPresheaf` (`h_V` is the presheaf of solutions of
the presentation), followed by
`AlgebraicGeometry.geometricFiberSolutionsEquiv` (the fibre of the presheaf of solutions is the
solution set over the étale local ring).

Since the étale local ring is strictly henselian
(`AlgebraicGeometry.etaleLocalRing_strictHenselian`), this is the set to which
[Stacks Project, Tag 04GX] — `MvPolynomial.bijective_homOverMap_of_etale` — applies. -/
def geometricPointFiberEquivEtaleLocalSolutions (V : SmallEtale B S hS)
    [IsAffine ((SmallEtale.toScheme B S hS).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B S hS).obj V)
      (schemeStructureHom B S hS V) P) :
    (geometricPointFiber B S hS s).obj V ≃ EtaleLocalSolutions B S hS s P :=
  (((yonedaCompEtaleStalkPresheafFunctorIso B S hS s).app V).toEquiv).symm.trans
    ((((geometricPointSitePoint B S hS s).presheafFiber.mapIso
        (representableIsoSolutionPresheaf B S hS V pres)).toEquiv).trans
      (geometricFiberSolutionsEquiv B S hS s P))

end Representable

end AlgebraicGeometry

end
