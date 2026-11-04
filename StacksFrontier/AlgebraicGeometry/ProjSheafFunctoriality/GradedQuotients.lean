module

public import StacksFrontier.Algebra.DirectSum.GradedQuotient
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Abelian
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import StacksFrontier.RingTheory.AdicCompletion.LadderStableImage

/-!
# Quotients of graded modules, and graded modules modulo torsion

For a nonnegatively graded ring `S` this file adds to the category
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat` of `ℤ`-graded `S`-modules and
degree-preserving maps:

* the forgetful functor to `S`-modules;
* the quotient of a graded module by a homogeneous submodule, graded by the images of the graded
  pieces, and in particular the inverse system `(N / J^{n+1} N)` of adic quotients of a graded
  module by a homogeneous ideal `J`;
* for an ideal `J ⊆ S`, the class of degree-preserving maps whose kernel and cokernel are
  `J`-power torsion. The *category of graded `S`-modules modulo `J`-power torsion modules* is the
  localization of `GradedModuleCat` at this class: for `J` homogeneous the `J`-power torsion
  graded modules form a Serre subcategory, and the quotient of an abelian category by a Serre
  subcategory is its localization at the maps with kernel and cokernel in it
  ([Stacks, Tag 02MS]).

## Main definitions

* `GradedModuleCat.toModuleCat` — the forgetful functor.
* `GradedModuleCat.quotient` — the quotient by a homogeneous submodule.
* `GradedModuleCat.adicQuotients` — the inverse system `(N / J^{n+1} N)`.
* `GradedModuleCat.isoModTorsion` — the maps with `J`-power torsion kernel and cokernel.
* `GradedModuleCat.ofGrading`, `GradedModuleCat.liftSystem` — graded modules and inverse systems
  of them, from explicit gradings.

## Main results

* `GradedModuleCat.hasProLadder_of_toModuleCat` — a ladder of degree-preserving maps is a ladder
  of graded modules.

## Implementation notes

The kernel and the cokernel of a degree-preserving map are graded by the gradings of its source
and target, and their underlying modules are the kernel and the cokernel of the underlying linear
map; being `J`-power torsion depends only on the underlying module, so `isoModTorsion` is stated
on the underlying linear map.

The adic quotients are indexed from `0`, with term `n` the quotient by `J^{n+1}`, as for the
coherent adic systems of the library.

## References

* [Stacks Project, Tag 02MS](https://stacks.math.columbia.edu/tag/02MS)
* [Stacks Project, Tag 0EL4](https://stacks.math.columbia.edu/tag/0EL4)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.GradedLocalization

universe u v w

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The forgetful functor** from graded `S`-modules to `S`-modules. -/
public def toModuleCat : GradedModuleCat.{u, v, w} 𝒮 ⥤ ModuleCat.{v} S where
  obj M := ModuleCat.of S M.carrier
  map f := ModuleCat.ofHom f.toLinearMap

/-- The forgetful functor from graded `S`-modules to `S`-modules is faithful. -/
public instance : (toModuleCat 𝒮).Faithful where
  map_injective {_ _} _ _ h := hom_ext (congrArg ModuleCat.Hom.hom h)

/-- The grading of a graded module is compatible with the grading of `S`, read with the degree
of the product written as a sum of integers. -/
public theorem smul_mem_grade (M : GradedModuleCat.{u, v, w} 𝒮) {i : ℕ} {d : ℤ} {a : S}
    {x : M.carrier} (ha : a ∈ 𝒮 i) (hx : x ∈ M.grade d) : a • x ∈ M.grade ((i : ℤ) + d) :=
  SetLike.GradedSMul.smul_mem ha hx

/-- **The quotient of a graded module by a homogeneous submodule**, graded by the images of the
graded pieces. -/
public def quotient (M : GradedModuleCat.{u, v, w} 𝒮) (K : Submodule S M.carrier)
    (hK : K.IsHomogeneous M.grade) : GradedModuleCat.{u, v, w} 𝒮 where
  carrier := M.carrier ⧸ K
  grade := Submodule.gradedQuotientPiece M.grade K
  decomposition := (Submodule.isInternal_gradedQuotientPiece M.grade hK).chooseDecomposition
  gradedSMul := ⟨fun {_ _ _ _} ha hz =>
    Submodule.smul_mem_gradedQuotientPiece 𝒮 M.grade
      (fun _ _ _ _ ha hx => smul_mem_grade 𝒮 M ha hx) K ha hz⟩

/-- The projection onto a quotient by a homogeneous submodule, a degree-preserving map. -/
public def quotientπ (M : GradedModuleCat.{u, v, w} 𝒮) (K : Submodule S M.carrier)
    (hK : K.IsHomogeneous M.grade) : M ⟶ quotient 𝒮 M K hK where
  toLinearMap := K.mkQ
  map_grade _ _ hm := Submodule.mkQ_mem_gradedQuotientPiece M.grade hm

/-- The map between quotients of a graded module induced by an inclusion of homogeneous
submodules. -/
public def quotientMap (M : GradedModuleCat.{u, v, w} 𝒮) {K K' : Submodule S M.carrier}
    (hK : K.IsHomogeneous M.grade) (hK' : K'.IsHomogeneous M.grade) (h : K ≤ K') :
    quotient 𝒮 M K hK ⟶ quotient 𝒮 M K' hK' where
  toLinearMap := Submodule.factor h
  map_grade _ _ := by
    rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The submodule `J^{n+1} N` of a graded module, for a homogeneous ideal `J`, is homogeneous. -/
public theorem isHomogeneous_pow_smul_top (N : GradedModuleCat.{u, v, w} 𝒮) {J : Ideal S}
    (hJ : J.IsHomogeneous 𝒮) (n : ℕ) :
    (J ^ (n + 1) • (⊤ : Submodule S N.carrier)).IsHomogeneous N.grade :=
  Submodule.isHomogeneous_smul_top 𝒮 N.grade (fun _ _ _ _ ha hx => smul_mem_grade 𝒮 N ha hx)
    (hJ.pow 𝒮 _)

/-- The powers of an ideal times a module decrease. -/
public theorem pow_succ_smul_top_le (N : GradedModuleCat.{u, v, w} 𝒮) (J : Ideal S) {n m : ℕ}
    (h : n ≤ m) :
    J ^ (m + 1) • (⊤ : Submodule S N.carrier) ≤ J ^ (n + 1) • (⊤ : Submodule S N.carrier) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.succ_le_succ h))

/-- **The inverse system `(N / J^{n+1} N)` of adic quotients** of a graded module by a homogeneous
ideal, with the canonical projections as transition maps. -/
public def adicQuotients (N : GradedModuleCat.{u, v, w} 𝒮) (J : Ideal S) (hJ : J.IsHomogeneous 𝒮) :
    ℕᵒᵖ ⥤ GradedModuleCat.{u, v, w} 𝒮 where
  obj n := quotient 𝒮 N (J ^ (n.unop + 1) • ⊤) (isHomogeneous_pow_smul_top 𝒮 N hJ n.unop)
  map f := quotientMap 𝒮 N _ _ (pow_succ_smul_top_le 𝒮 N J (leOfHom f.unop))
  map_id _ := hom_ext (Submodule.mapQ_id _)
  map_comp f g := hom_ext
    (Submodule.factor_comp (pow_succ_smul_top_le 𝒮 N J (leOfHom f.unop))
      (pow_succ_smul_top_le 𝒮 N J (leOfHom g.unop))).symm

/-- The projections of a graded module onto its adic quotients. -/
public def adicQuotientsπ (N : GradedModuleCat.{u, v, w} 𝒮) (J : Ideal S)
    (hJ : J.IsHomogeneous 𝒮) (n : ℕ) : N ⟶ (adicQuotients 𝒮 N J hJ).obj (op n) :=
  quotientπ 𝒮 N (J ^ (n + 1) • ⊤) (isHomogeneous_pow_smul_top 𝒮 N hJ n)

/-- The underlying linear map of a projection onto an adic quotient is the quotient map. -/
public theorem adicQuotientsπ_toLinearMap (N : GradedModuleCat.{u, v, w} 𝒮) (J : Ideal S)
    (hJ : J.IsHomogeneous 𝒮) (n : ℕ) :
    (adicQuotientsπ 𝒮 N J hJ n).toLinearMap = (J ^ (n + 1) • (⊤ : Submodule S N.carrier)).mkQ :=
  rfl

/-- The transition maps of the adic quotients send the class of an element to its class. -/
public theorem adicQuotients_map_mk (N : GradedModuleCat.{u, v, w} 𝒮) (J : Ideal S)
    (hJ : J.IsHomogeneous 𝒮) {n m : ℕᵒᵖ} (f : n ⟶ m) (x : N.carrier) :
    ((adicQuotients 𝒮 N J hJ).map f).toLinearMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  rfl

/-- **The maps of graded modules with `J`-power torsion kernel and cokernel.** Localizing
`GradedModuleCat` at this class gives the category of graded modules modulo `J`-power torsion
modules. -/
public def isoModTorsion (J : Ideal S) : MorphismProperty (GradedModuleCat.{u, v, w} 𝒮) :=
  fun _ N f => IsIPowerTorsion S (LinearMap.ker f.toLinearMap) J ∧
    IsIPowerTorsion S (N.carrier ⧸ LinearMap.range f.toLinearMap) J

/-! ### Graded modules and inverse systems from explicit gradings -/

/-- The graded module given by a module, a decomposition of it into additive subgroups indexed by
`ℤ`, and the compatibility of that decomposition with the grading of `S`. -/
public def ofGrading (M : Type v) [AddCommGroup M] [Module S M] (ℳ : ℤ → AddSubgroup M)
    [DirectSum.Decomposition ℳ]
    (hℳ : ∀ (i : ℕ) (d : ℤ) (a : S) (x : M), a ∈ 𝒮 i → x ∈ ℳ d → a • x ∈ ℳ ((i : ℤ) + d)) :
    GradedModuleCat.{u, v, w} 𝒮 where
  carrier := M
  grade := ℳ
  gradedSMul := ⟨fun {i d a x} ha hx => hℳ i d a x ha hx⟩

/-- **An inverse system of modules with degree-preserving transitions is an inverse system of
graded modules.** -/
public def liftSystem (D : ℕᵒᵖ ⥤ ModuleCat.{v} S) (𝒟 : ∀ n : ℕ, ℤ → AddSubgroup (D.obj (op n)))
    [∀ n : ℕ, DirectSum.Decomposition (𝒟 n)]
    (h𝒟 : ∀ (n i : ℕ) (d : ℤ) (a : S) (x : D.obj (op n)), a ∈ 𝒮 i → x ∈ 𝒟 n d →
      a • x ∈ 𝒟 n ((i : ℤ) + d))
    (htr : ∀ (n m : ℕ) (h : n ≤ m) (d : ℤ) (x : D.obj (op m)), x ∈ 𝒟 m d →
      Stacks.ProObject.tr D h x ∈ 𝒟 n d) :
    ℕᵒᵖ ⥤ GradedModuleCat.{u, v, w} 𝒮 where
  obj n := ofGrading 𝒮 (D.obj n) (𝒟 n.unop) (h𝒟 n.unop)
  map {n m} f :=
    { toLinearMap := (D.map f).hom
      map_grade := fun d x hx => by
        have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        rw [hf]
        exact htr m.unop n.unop (leOfHom f.unop) d x hx }
  map_id n := hom_ext (congrArg ModuleCat.Hom.hom (D.map_id n))
  map_comp f g := hom_ext (congrArg ModuleCat.Hom.hom (D.map_comp f g))

/-- **A ladder of degree-preserving maps is a ladder of graded modules.** A ladder between the
underlying inverse systems of modules of two inverse systems of graded modules, whose maps
preserve degrees, lifts to a ladder of graded modules: the forgetful functor is faithful. -/
public theorem hasProLadder_of_toModuleCat {A B : ℕᵒᵖ ⥤ GradedModuleCat.{u, v, w} 𝒮}
    (L : Stacks.ProObject.LadderData (A ⋙ toModuleCat 𝒮) (B ⋙ toModuleCat 𝒮))
    (hf : ∀ (k : ℕ) (d : ℤ) (x : (A.obj (op (L.p k))).carrier),
      x ∈ (A.obj (op (L.p k))).grade d → (L.f k).hom x ∈ (B.obj (op k)).grade d)
    (hg : ∀ (n : ℕ) (d : ℤ) (x : (B.obj (op (L.q n))).carrier),
      x ∈ (B.obj (op (L.q n))).grade d → (L.g n).hom x ∈ (A.obj (op n)).grade d) :
    Stacks.ProObject.HasProLadder A B := by
  refine ⟨L.p, fun k => ⟨(L.f k).hom, hf k⟩, L.q,
    fun n => ⟨(L.g n).hom, hg n⟩, ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    exact (L.cf n m hnm).imp fun _ => .imp fun _ => .imp fun _ hk =>
      hom_ext (congrArg ModuleCat.Hom.hom hk)
  · intro n m hnm
    exact (L.cg n m hnm).imp fun _ => .imp fun _ => .imp fun _ hk =>
      hom_ext (congrArg ModuleCat.Hom.hom hk)
  · intro n
    exact (L.fg n).imp fun _ => .imp fun _ => .imp fun _ hk =>
      hom_ext (congrArg ModuleCat.Hom.hom hk)
  · intro n
    exact (L.gf n).imp fun _ => .imp fun _ => .imp fun _ hk =>
      hom_ext (congrArg ModuleCat.Hom.hom hk)


end Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat

end
