module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Deformation.AlgebraExtension.Basic

/-!
# The map of ideals induced by a homomorphism of extensions

Let `P` and `Q` be extensions of `𝒜`-algebras of `𝒪` by `ℳ` and by `𝒩`. A homomorphism
`h : 𝒪'_P ⟶ 𝒪'_Q` of the middle terms over `𝒪` carries the kernel of the reduction of `P` into
the kernel of the reduction of `Q`, hence induces a map of `𝒪`-modules `ℳ ⟶ 𝒩`; if `h` is also
under `𝒜`, it is a morphism of extensions along that map. The induced map is the only map of
modules along which `h` is a morphism of extensions, so a morphism of extensions along `φ` is
along the induced map exactly when `φ` is the induced map.

## Main definitions

* `Deformation.AlgebraExtension.inducedKernelMap`: the map of ideals induced by a homomorphism of
  middle terms over `𝒪`.
* `Deformation.AlgebraExtension.mapAlongInducedKernelMap`: the morphism of extensions along it.

## Main results

* `Deformation.AlgebraExtension.MapAlong.eq_inducedKernelMap`: a morphism of extensions along `φ`
  has `φ` the induced map of its homomorphism of middle terms.
* `Deformation.AlgebraExtension.MapAlong.eq_of_hom_eq`: two morphisms of extensions with the same
  homomorphism of middle terms are along the same map of ideals.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace Deformation.AlgebraExtension

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

section KernelMap

/- The map of ideals only sees the reductions, so the two extensions may be over different
bases. -/
variable {A' : Sheaf J CommRingCat.{u}} {a' : A' ⟶ O}
  (P : AlgebraExtension a M) (Q : AlgebraExtension a' N)
  (h : P.extension ⟶ Q.extension) (hh : h ≫ Q.reduction = P.reduction)

include hh in
/-- A homomorphism of middle terms over `𝒪` commutes with the reductions on sections. -/
private theorem reduction_hom_app {U : Cᵒᵖ} (x : P.extension.obj.obj U) :
    Q.reduction.hom.app U (h.hom.app U x) = P.reduction.hom.app U x :=
  congrArg (fun k : P.extension ⟶ O => k.hom.app U x) hh

include hh in
/-- A homomorphism of middle terms over `𝒪` carries the ideal of `P` into the kernel of the
reduction of `Q`. -/
theorem reduction_hom_incl {U : Cᵒᵖ} (m : M.val.obj U) :
    Q.reduction.hom.app U (h.hom.app U (P.incl m)) = 0 :=
  (reduction_hom_app P Q h hh _).trans (P.reduction_incl m)

/-- The value on a section of the map of ideals induced by `h`. -/
noncomputable def inducedKernelSection {U : Cᵒᵖ} (m : M.val.obj U) : N.val.obj U :=
  (Q.exists_incl _ (reduction_hom_incl P Q h hh m)).choose

/-- The image under `Q.incl` of the induced section of `m` is `h (P.incl m)`. -/
theorem incl_inducedKernelSection {U : Cᵒᵖ} (m : M.val.obj U) :
    Q.incl (inducedKernelSection P Q h hh m) = h.hom.app U (P.incl m) :=
  (Q.exists_incl _ (reduction_hom_incl P Q h hh m)).choose_spec

/-- A section `n` with `Q.incl n = h (P.incl m)` is the induced section of `m`. -/
theorem inducedKernelSection_eq {U : Cᵒᵖ} (m : M.val.obj U) (n : N.val.obj U)
    (hn : Q.incl n = h.hom.app U (P.incl m)) : inducedKernelSection P Q h hh m = n :=
  Q.incl_injective ((incl_inducedKernelSection P Q h hh m).trans hn.symm)

/-- The induced sections commute with restriction. -/
theorem inducedKernelSection_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (m : M.val.obj U) :
    N.val.map f (inducedKernelSection P Q h hh m) =
      inducedKernelSection P Q h hh (U := V) (M.val.map f m) := by
  refine (inducedKernelSection_eq P Q h hh (U := V) (M.val.map f m) _ ?_).symm
  rw [Q.incl_naturality, incl_inducedKernelSection, P.incl_naturality]
  exact (NatTrans.naturality_apply h.hom f _).symm

/-- The induced sections are additive. -/
theorem inducedKernelSection_add {U : Cᵒᵖ} (m n : M.val.obj U) :
    inducedKernelSection P Q h hh (m + n) =
      inducedKernelSection P Q h hh m + inducedKernelSection P Q h hh n := by
  refine inducedKernelSection_eq P Q h hh (m + n) _ ?_
  rw [Q.incl_add, incl_inducedKernelSection, incl_inducedKernelSection, P.incl_add, map_add]

/-- The induced map is linear for the scalars that lift to the middle term of `P`. -/
theorem inducedKernelSection_reduction_smul {U : Cᵒᵖ} (x : P.extension.obj.obj U)
    (m : M.val.obj U) :
    inducedKernelSection P Q h hh (scalar (P.reduction.hom.app U x) • m) =
      scalar (P.reduction.hom.app U x) • inducedKernelSection P Q h hh m := by
  refine inducedKernelSection_eq P Q h hh (scalar (P.reduction.hom.app U x) • m) _ ?_
  calc Q.incl (scalar (P.reduction.hom.app U x) • inducedKernelSection P Q h hh m)
      = Q.incl (scalar (Q.reduction.hom.app U (h.hom.app U x)) •
          inducedKernelSection P Q h hh m) := by rw [reduction_hom_app P Q h hh x]
    _ = h.hom.app U x * h.hom.app U (P.incl m) := by
        rw [← Q.mul_incl, incl_inducedKernelSection]
    _ = h.hom.app U (P.incl (scalar (P.reduction.hom.app U x) • m)) := by
        rw [← map_mul, P.mul_incl]

/-- The induced sections are linear over `𝒪`. -/
theorem inducedKernelSection_smul {U : Cᵒᵖ} (r : O.obj.obj U) (m : M.val.obj U) :
    inducedKernelSection P Q h hh (scalar r • m) = scalar r • inducedKernelSection P Q h hh m := by
  have hsep : Presheaf.IsSeparated J N.val.presheaf := Presheaf.IsSheaf.isSeparated N.isSheaf
  refine hsep U.unop _ (P.locallySurjective.imageSieve_mem r) _ _ fun Y g hg => ?_
  obtain ⟨x, hx⟩ := hg
  show N.val.map g.op _ = N.val.map g.op _
  rw [inducedKernelSection_naturality, PresheafOfModules.map_smul, PresheafOfModules.map_smul,
    inducedKernelSection_naturality]
  have hx' : scalar (P.reduction.hom.app (op Y) x) =
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.map g.op r := hx
  rw [← hx']
  exact inducedKernelSection_reduction_smul P Q h hh x _

/-- **The map of ideals induced by a homomorphism of middle terms over `𝒪`.** -/
noncomputable def inducedKernelMap : M ⟶ N where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := inducedKernelSection P Q h hh
          map_add' := inducedKernelSection_add P Q h hh
          map_smul' := inducedKernelSection_smul P Q h hh }
      naturality := fun {U V} f => ModuleCat.hom_ext (LinearMap.ext fun m =>
        (inducedKernelSection_naturality P Q h hh f m).symm) }

/-- On sections, the induced map of ideals is `inducedKernelSection`. -/
theorem inducedKernelMap_val_app {U : Cᵒᵖ} (m : M.val.obj U) :
    (inducedKernelMap P Q h hh).val.app U m = inducedKernelSection P Q h hh m :=
  rfl

/-- The homomorphism `h` restricted to the ideal of `P` is `Q.incl` composed with the induced map
of ideals. -/
theorem hom_incl {U : Cᵒᵖ} (m : M.val.obj U) :
    h.hom.app U (P.incl m) = Q.incl ((inducedKernelMap P Q h hh).val.app U m) :=
  (incl_inducedKernelSection P Q h hh m).symm

/-- **A locally surjective homomorphism of middle terms induces a locally surjective map of
ideals.** -/
theorem isLocallySurjective_inducedKernelMap (hs : Presheaf.IsLocallySurjective J h.hom) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (inducedKernelMap P Q h hh).val) where
  imageSieve_mem {U} n := by
    refine J.superset_covering ?_ (hs.imageSieve_mem (Q.incl (U := op U) n))
    rintro V g ⟨x, hx⟩
    have hr : P.reduction.hom.app (op V) x = 0 := by
      rw [← reduction_hom_app P Q h hh x, hx, NatTrans.naturality_apply]
      exact (congrArg (O.obj.map g.op) (Q.reduction_incl (U := op U) n)).trans (map_zero _)
    obtain ⟨m, rfl⟩ := P.exists_incl x hr
    exact ⟨m, inducedKernelSection_eq P Q h hh m _ ((Q.incl_naturality g.op n).trans hx.symm)⟩

/-- **A locally surjective homomorphism of middle terms induces an epimorphism of ideals.** -/
theorem epi_inducedKernelMap [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (hs : Presheaf.IsLocallySurjective J h.hom) :
    Epi (inducedKernelMap P Q h hh) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (isLocallySurjective_inducedKernelMap P Q h hh hs)

/-- **The five lemma on sections.** If over `U` the reduction of `P` and the induced map of ideals
are surjective, so is the homomorphism `h` of middle terms over `U`. -/
theorem surjective_hom_app_of_surjective {U : Cᵒᵖ}
    (hP : Function.Surjective (P.reduction.hom.app U))
    (hk : Function.Surjective ((inducedKernelMap P Q h hh).val.app U)) :
    Function.Surjective (h.hom.app U) := by
  intro y
  obtain ⟨x, hx⟩ := hP (Q.reduction.hom.app U y)
  obtain ⟨n, hn⟩ := Q.exists_incl (y - h.hom.app U x)
    (by rw [map_sub, reduction_hom_app P Q h hh x, hx, sub_self])
  obtain ⟨m, rfl⟩ := hk n
  refine ⟨x + P.incl m, ?_⟩
  rw [map_add, hom_incl P Q h hh m, hn, add_sub_cancel]

end KernelMap

section MapAlong

variable (P : AlgebraExtension a M) (Q : AlgebraExtension a N)
  (h : P.extension ⟶ Q.extension) (hh : h ≫ Q.reduction = P.reduction)

/-- **A homomorphism of middle terms over `𝒪` and under `𝒜` is a morphism of extensions** along
the map of ideals it induces. -/
noncomputable def mapAlongInducedKernelMap (ha : P.algebraMap ≫ h = Q.algebraMap) :
    MapAlong (inducedKernelMap P Q h hh) P Q where
  hom := h
  reduction_comm := hh
  algebraMap_comm := ha
  kernel_comm _ m := hom_incl P Q h hh m

/-- **A morphism of extensions along `φ` has `φ` the map of ideals induced by its homomorphism of
middle terms.** -/
theorem MapAlong.eq_inducedKernelMap {φ : M ⟶ N} (g : MapAlong φ P Q) :
    φ = inducedKernelMap P Q g.hom g.reduction_comm := by
  ext U m
  exact (inducedKernelSection_eq P Q g.hom g.reduction_comm _ _ (g.kernel_comm U m).symm).symm

/-- A homomorphism of middle terms over `𝒪` and under `𝒜` is a morphism of extensions along `φ`
as soon as `φ` is the map of ideals it induces. -/
noncomputable def mapAlongOfEq {φ : M ⟶ N} (ha : P.algebraMap ≫ h = Q.algebraMap)
    (hφ : inducedKernelMap P Q h hh = φ) : MapAlong φ P Q :=
  hφ ▸ mapAlongInducedKernelMap P Q h hh ha

end MapAlong

end Deformation.AlgebraExtension
