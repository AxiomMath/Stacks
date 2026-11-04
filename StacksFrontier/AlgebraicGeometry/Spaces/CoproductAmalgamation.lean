module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued

/-!
# Glueing a family of points of a sheaf along a coproduct of objects of the site

Let `S` be a scheme contained in a big fppf site `B`. A family of objects `V i` of the big
fppf site over `S` whose coproduct of underlying schemes still lies in `B` has that coproduct
for an object `W` of the site, and the component inclusions `V i ⟶ W` form a jointly
surjective family of *pairwise disjoint* open immersions. A family of points of a sheaf on the
site, one over each `V i`, glues to a single point over `W`.

## Main results

* `AlgebraicGeometry.Space.subsingleton_sections_of_isEmpty`: a sheaf on the big fppf site of
  `S` has at most one section over an object whose underlying scheme is empty.
* `AlgebraicGeometry.Space.exists_amalgamation_of_disjoint_openCover`: a family of points of a
  sheaf over a pairwise disjoint open cover of an object of the site glues to a point over
  that object.
* `AlgebraicGeometry.Space.exists_map_from_coproduct`: the same with the cover constructed, as
  the component inclusions of a coproduct of objects of the site.
* `AlgebraicGeometry.Space.hom_ext_of_openCover`: two points of a sheaf agreeing on each member
  of a jointly surjective family of open immersions are equal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two sections of a sheaf over `U` agreeing on every member of a covering family of arrows
are equal. -/
private theorem eq_of_map_eq_of_ofArrows_mem
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    {I : Type*} {U : BigFppfOver B S hS} {V : I → BigFppfOver B S hS} (k : ∀ i, V i ⟶ U)
    (hmem : Sieve.ofArrows V k ∈ BigFppfOver.topology B S hS U)
    {x y : X.obj.obj (Opposite.op U)} (h : ∀ i, X.obj.map (k i).op x = X.obj.map (k i).op y) :
    x = y :=
  ConcreteCategory.congr_hom
    (X.property.hom_ext_ofArrows k hmem (x := (↾fun _ : PUnit.{u + 2} => x))
      (y := (↾fun _ : PUnit.{u + 2} => y)) fun i => by ext _; exact h i) PUnit.unit

/-- A sheaf on the big fppf site of `S` has at most one section over an object of the site
whose underlying scheme is empty. -/
theorem subsingleton_sections_of_isEmpty
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (U : BigFppfOver B S hS)
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj U)] :
    Subsingleton (X.obj.obj (Opposite.op U)) := by
  exact ⟨fun x y => eq_of_map_eq_of_ofArrows_mem B S hS X (V := fun _ : PEmpty.{u + 1} => U)
    (fun i => i.elim)
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS
      (fun i : PEmpty.{u + 1} => i.elim) (fun i => i.elim) (fun x => isEmptyElim x))
    (fun i => i.elim)⟩

/-- A family of points of a sheaf on the big fppf site of `S`, one over each member of a
jointly surjective family of pairwise disjoint open immersions into an object `W` of the site,
glues to a single point over `W` restricting to the given ones. -/
theorem exists_amalgamation_of_disjoint_openCover
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    {I : Type u} {W : BigFppfOver B S hS} (V : I → BigFppfOver B S hS) (k : ∀ i, V i ⟶ W)
    (hk : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (k i)))
    (hcov : ∀ w : (BigFppfOver.toScheme B S hS).obj W,
      ∃ i, w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (k i)))
    (hdisj : ∀ i j, i ≠ j → ∀ (z : (BigFppfOver.toScheme B S hS).obj (V i))
      (z' : (BigFppfOver.toScheme B S hS).obj (V j)),
      (BigFppfOver.toScheme B S hS).map (k i) z ≠ (BigFppfOver.toScheme B S hS).map (k j) z')
    (f : ∀ i, (uliftYoneda.{u + 1}).obj (V i) ⟶ X.obj) :
    ∃ q : (uliftYoneda.{u + 1}).obj W ⟶ X.obj,
      ∀ i, (uliftYoneda.{u + 1}).map (k i) ≫ q = f i := by
  classical
  have hmem := BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS k hk hcov
  let x (i : I) : PUnit.{u + 2} ⟶ X.obj.obj (Opposite.op (V i)) :=
    ↾fun _ => uliftYonedaEquiv (f i)
  have hx : ∀ ⦃T⦄ ⦃i j⦄ (a : T ⟶ V i) (b : T ⟶ V j),
      a ≫ k i = b ≫ k j → x i ≫ X.obj.map a.op = x j ≫ X.obj.map b.op := by
    intro T i j a b hab
    by_cases hij : i = j
    · subst j
      have hm : Mono ((BigFppfOver.toScheme B S hS).map (k i)) := by
        have := hk i; infer_instance
      have : Mono (k i).left := B.inclusion.mono_of_mono_map hm
      have : Mono (k i) := Over.mono_of_mono_left _
      rw [(cancel_mono (k i)).mp hab]
    · have hw : (BigFppfOver.toScheme B S hS).map a ≫
          (BigFppfOver.toScheme B S hS).map (k i) =
            (BigFppfOver.toScheme B S hS).map b ≫
              (BigFppfOver.toScheme B S hS).map (k j) := by
        rw [← Functor.map_comp, ← Functor.map_comp, hab]
      have : IsEmpty ((BigFppfOver.toScheme B S hS).obj T) :=
        ⟨fun z => hdisj i j hij ((BigFppfOver.toScheme B S hS).map a z)
          ((BigFppfOver.toScheme B S hS).map b z) (by
            rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply])⟩
      have := subsingleton_sections_of_isEmpty B S hS X T
      ext z
      exact Subsingleton.elim _ _
  obtain ⟨z, hz, -⟩ := X.property.existsUnique_amalgamation_ofArrows k hmem x hx
  refine ⟨uliftYonedaEquiv.symm (z PUnit.unit), fun i => uliftYonedaEquiv.injective ?_⟩
  exact (uliftYonedaEquiv_naturality.{u + 1}
    (uliftYonedaEquiv.symm (z PUnit.unit)) (k i).op).symm.trans
      (by simpa [x] using ConcreteCategory.congr_hom (hz i) PUnit.unit)

/-- A family of points of a sheaf on the big fppf site of `S`, indexed by a type in the
universe of the schemes and with the coproduct of the underlying schemes of the sources still
in the site, glues to a single point over that coproduct; the component inclusions into the
coproduct are pairwise disjoint, jointly surjective open immersions. -/
theorem exists_map_from_coproduct
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    {I : Type u} (V : I → BigFppfOver B S hS)
    (f : ∀ i, (uliftYoneda.{u + 1}).obj (V i) ⟶ X.obj)
    (hsize : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (V i))) :
    ∃ (W : BigFppfOver B S hS) (k : ∀ i, V i ⟶ W)
      (q : (uliftYoneda.{u + 1}).obj W ⟶ X.obj),
      (∀ i, (uliftYoneda.{u + 1}).map (k i) ≫ q = f i) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (k i))) ∧
      (∀ w : (BigFppfOver.toScheme B S hS).obj W,
        ∃ i, w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (k i))) ∧
      (∀ i j, i ≠ j → ∀ (z : (BigFppfOver.toScheme B S hS).obj (V i))
        (z' : (BigFppfOver.toScheme B S hS).obj (V j)),
        (BigFppfOver.toScheme B S hS).map (k i) z ≠
          (BigFppfOver.toScheme B S hS).map (k j) z') := by
  classical
  let D := fun i => (BigFppfOver.toScheme B S hS).obj (V i)
  let W : BigFppfOver B S hS :=
    Over.mk (Y := B.obj hsize) (X := B.obj hS)
      (ObjectProperty.homMk (Sigma.desc fun i => (V i).hom.hom))
  let k (i : I) : V i ⟶ W := Over.homMk (ObjectProperty.homMk (Sigma.ι D i)) (by
    apply ObjectProperty.hom_ext
    exact Sigma.ι_desc _ _)
  have hk (i : I) : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (k i)) := by
    show _root_.AlgebraicGeometry.IsOpenImmersion (Sigma.ι D i)
    infer_instance
  have hcov : ∀ w : (BigFppfOver.toScheme B S hS).obj W,
      ∃ i, w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (k i)) :=
    (sigmaOpenCover D).exists_eq
  have hdisj : ∀ i j, i ≠ j → ∀ (z : D i) (z' : D j),
      (BigFppfOver.toScheme B S hS).map (k i) z ≠
        (BigFppfOver.toScheme B S hS).map (k j) z' := fun i j hij z z' hz =>
    hij (congrArg Sigma.fst ((sigmaι_eq_iff D i j z z').mp hz))
  obtain ⟨q, hq⟩ := exists_amalgamation_of_disjoint_openCover B S hS X V k hk hcov hdisj f
  exact ⟨W, k, q, hq, hk, hcov, hdisj⟩

/-- Two points of a sheaf over an object of the site agreeing on each member of a jointly
surjective family of open immersions are equal. -/
theorem hom_ext_of_openCover
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    {I : Type u} {W : BigFppfOver B S hS} (V : I → BigFppfOver B S hS) (k : ∀ i, V i ⟶ W)
    (hk : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (k i)))
    (hcov : ∀ w : (BigFppfOver.toScheme B S hS).obj W,
      ∃ i, w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (k i)))
    {g g' : (uliftYoneda.{u + 1}).obj W ⟶ X.obj}
    (h : ∀ i, (uliftYoneda.{u + 1}).map (k i) ≫ g = (uliftYoneda.{u + 1}).map (k i) ≫ g') :
    g = g' := by
  classical
  have hmem := BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS k hk hcov
  apply uliftYonedaEquiv.injective
  refine eq_of_map_eq_of_ofArrows_mem B S hS X k hmem fun i => ?_
  rw [uliftYonedaEquiv_naturality.{u + 1} g (k i).op,
    uliftYonedaEquiv_naturality.{u + 1} g' (k i).op]
  simp only [Quiver.Hom.unop_op, h i]

end AlgebraicGeometry.Space

end
