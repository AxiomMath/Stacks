module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# The affine dictionary between pullback of associated sheaves and module base change

Let `φ : R ⟶ S` be a map of commutative rings and let `M` be an `R`-module. Pulling the
associated sheaf `M̃` back along `Spec φ` gives the sheaf associated to the base change
`S ⊗_R M`; `AlgebraicGeometry.pullbackTildeIso` records this as a natural isomorphism of
functors. This file turns that natural isomorphism into the dictionary a consumer actually
uses: the isomorphism at a single module, the induced identification of global sections, and
the normalizations that say what the identification does to elements.

Concretely, the global sections of `(Spec φ)^* M̃` are `S ⊗_R M`, by an `S`-linear equivalence
that carries the canonical section `1 ⊗ m` -- the image of the global section of `M̃`
represented by `m` under the pullback--pushforward adjunction unit -- to the pure tensor
`1 ⊗ m`. Since the equivalence is `S`-linear and those canonical sections span, this pins the
identification down on every section.

## Main definitions

* `AlgebraicGeometry.extendScalarsTensorEquiv`: the underlying module of
  `ModuleCat.extendScalars (algebraMap R S)` is the plain tensor product `S ⊗[R] M`.
* `AlgebraicGeometry.pullbackTildeComponent`: the affine pullback isomorphism at a single
  module, `(Spec φ)^* M̃ ≅ (S ⊗_R M)~`.
* `AlgebraicGeometry.pullbackTildeΓIso`: the induced isomorphism of `S`-modules between the
  global sections of `(Spec φ)^* M̃` and `ModuleCat.extendScalars φ.hom` of `M`.
* `AlgebraicGeometry.pullbackTildeΓEquiv`: that isomorphism as an `S`-linear equivalence.
* `AlgebraicGeometry.pullbackTildeΓUnit`: the canonical global section `1 ⊗ m` of
  `(Spec φ)^* M̃` attached to an element `m` of `M`.
* `AlgebraicGeometry.pullbackTildeΓTensorEquiv`: the same identification with the plain tensor
  product `S ⊗[R] M` as its target, for `R` and `S` presented as rings with an algebra
  structure.

## Main results

* `AlgebraicGeometry.pullbackTildeΓEquiv_unit` and
  `AlgebraicGeometry.pullbackTildeΓEquiv_symm_one_tmul` normalize the equivalence: it matches
  `pullbackTildeΓUnit m` with the pure tensor `1 ⊗ m`.
* `AlgebraicGeometry.pullbackTildeΓEquiv_smul_unit` and
  `AlgebraicGeometry.pullbackTildeΓEquiv_symm_tmul` read off the general pure tensor: `s ⊗ m`
  corresponds to `s • pullbackTildeΓUnit m`.
* `AlgebraicGeometry.span_range_pullbackTildeΓUnit`: the canonical sections span all global
  sections of the pullback over `S`, so those normalizations determine the equivalence.
* `AlgebraicGeometry.pullbackTildeΓTensorEquiv_unit` and
  `AlgebraicGeometry.pullbackTildeΓTensorEquiv_symm_one_tmul` are the same normalization for
  the plain tensor product.

## Implementation notes

Invertibility is carried throughout by an `Iso` or a `LinearEquiv` and never by an `IsIso`
instance: an `IsIso` introduced by `haveI` does not survive between separate elaborations.

The scalar ring is the bundled `CommRingCat` object wherever the sheaf side is involved. The
`Module ↑S Γ(F, ⊤)` instance of a module `F` on `Spec S` is indexed by that bundled object, so
for an unbundled `S` it is not found -- `S` and `↑(CommRingCat.of S)` agree only up to
unfolding, which instance search does not do. Most statements below therefore keep the bundled
form. `pullbackTildeΓTensorEquiv` is phrased for an unbundled algebra, because its target
`S ⊗[R] M` is, and so writes its source through `moduleSpecΓFunctor`, whose `Module` instance
is indexed by the module object instead and hence is found; for the same reason it carries no
`s • _` normalization, only the one at `1 ⊗ m`, scalar multiplication of a section not being
expressible there. The bundled `pullbackTildeΓEquiv_smul_unit` covers that case. It does apply
to a section written with the `Γ(-, ⊤)` notation, the two sources being definitionally equal,
but then `S` has to be supplied by name: the coercion standing between the two spellings
blocks its inference from the argument.

`extendScalarsTensorEquiv` is the unbundled half: `ModuleCat.extendScalars` forms its tensor
product against the restriction of scalars of `S` as an `S`-module, so its underlying module is
`((restrictScalars) S) ⊗[R] M` rather than `S ⊗[R] M`. The two differ only in the `Module R S`
instance, hence the comparison is the identity on pure tensors; what has to be checked is that
it is `S`-linear and not merely `R`-linear, which is why the `S`-action is transported onto the
tensor product explicitly before the structure is assembled.

For the same reason -- the `⊗ₜ[R, f]` notation builds its middle factor as `S` with a
`Module.compHom` action, while `ModuleCat.extendScalars` builds it as a restriction of scalars
-- a pure tensor appearing in a goal is often not syntactically the one a `rw` expects, even
though the two are definitionally equal. Where that happens the step is taken by `exact` with
`ModuleCat.ExtendScalars.smul_tmul` as a term rather than by `rw`, and the tensor-induction
case of `span_range_pullbackTildeΓUnit` is discharged through a hypothesis stated with the
coefficient at `↑S`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u

/-- The inverse of `AlgebraicGeometry.tilde.isoTop` undoes `AlgebraicGeometry.tilde.toOpen` at
the top open: `tilde.isoTop` is by definition `tilde.toOpen _ ⊤` promoted to an isomorphism. -/
public theorem tilde.isoTop_inv_toOpen {R : CommRingCat.{u}} (N : ModuleCat R) (n : N) :
    (tilde.isoTop N).inv.hom ((tilde.toOpen N ⊤).hom n) = n := by
  simpa [tilde.isoTop_hom] using congrArg (fun g ↦ g.hom n) (tilde.isoTop N).hom_inv_id

/-- The underlying module of an extension of scalars along `algebraMap R S` is the plain tensor
product `S ⊗[R] M`. The comparison is the identity on pure tensors; only the `S`-action has to
be matched, the `S`-module structure on the left being the one carried by the `ModuleCat`
object. -/
public noncomputable def extendScalarsTensorEquiv {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} (CommRingCat.of R)) :
    ((ModuleCat.extendScalars (algebraMap R S)).obj M) ≃ₗ[S] S ⊗[R] M := by
  let A : Type u := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let : Module S (A ⊗[R] (M : Type u)) :=
    inferInstanceAs (Module S ((ModuleCat.extendScalars (algebraMap R S)).obj M : Type u))
  let eS : A ≃ₗ[R] S :=
    { AddEquiv.refl S with
      map_smul' r x := (Algebra.smul_def (R := R) (A := S) r x).symm }
  let e := TensorProduct.congr eS (LinearEquiv.refl R (M : Type u))
  have key : ∀ (s : S) (w : A ⊗[R] (M : Type u)), e (s • w) = s • e w := by
    intro s w
    induction w using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul a m => rfl
    | add w w' hw hw' => rw [smul_add, map_add, map_add, smul_add, hw, hw']
  exact { e.toAddEquiv with map_smul' := key }

/-- `extendScalarsTensorEquiv` sends a pure tensor of the extension of scalars to the same pure
tensor of `S ⊗[R] M`. -/
@[simp]
public theorem extendScalarsTensorEquiv_tmul {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} (CommRingCat.of R)) (s : S) (m : M) :
    extendScalarsTensorEquiv (S := S) M (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m := rfl

/-- The inverse of `extendScalarsTensorEquiv` sends a pure tensor of `S ⊗[R] M` to the same pure
tensor of the extension of scalars. -/
@[simp]
public theorem extendScalarsTensorEquiv_symm_tmul {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} (CommRingCat.of R)) (s : S) (m : M) :
    (extendScalarsTensorEquiv (S := S) M).symm (s ⊗ₜ[R] m) =
      s ⊗ₜ[R, algebraMap R S] m := rfl

variable (R S : CommRingCat.{u}) (φ : R ⟶ S) (M : ModuleCat R)

/-- The affine pullback dictionary at a single module: pulling `M̃` back along `Spec φ` gives
the sheaf associated to the base change of `M` along `φ`.

This is `AlgebraicGeometry.pullbackTildeIso` at `M`, named so that the identification can be
rewritten with instead of being rebuilt at each use site. -/
public noncomputable def pullbackTildeComponent :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  (pullbackTildeIso R S φ).app M

/-- The global sections of the pullback of `M̃` along `Spec φ` are the base change of `M`
along `φ`, as `S`-modules: apply `moduleSpecΓFunctor` to `pullbackTildeComponent` and undo
`AlgebraicGeometry.tilde.isoTop` on the right. -/
public noncomputable def pullbackTildeΓIso :
    (moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M)) ≅
      (ModuleCat.extendScalars φ.hom).obj M :=
  (moduleSpecΓFunctor (R := S)).mapIso (pullbackTildeComponent R S φ M) ≪≫
    (tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj M)).symm

/-- `pullbackTildeΓIso` as an `S`-linear equivalence on the sections themselves. -/
public noncomputable def pullbackTildeΓEquiv :
    Γ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M), ⊤) ≃ₗ[S]
      ((ModuleCat.extendScalars φ.hom).obj M) :=
  (pullbackTildeΓIso R S φ M).toLinearEquiv

/-- The canonical global section of `(Spec φ)^* M̃` attached to `m : M`, namely the image of the
global section of `M̃` represented by `m` under the unit of the pullback--pushforward
adjunction. It is the section that `pullbackTildeΓEquiv` sends to `1 ⊗ m`. -/
public noncomputable def pullbackTildeΓUnit (m : M) :
    Γ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M), ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
    (tilde M)).val.app (.op ⊤)).hom ((tilde.toOpen M ⊤).hom m)

/-- **The normalization of the affine pullback dictionary on global sections.** The canonical
section attached to `m` corresponds to the pure tensor `1 ⊗ m`. -/
@[simp]
public theorem pullbackTildeΓEquiv_unit (m : M) :
    pullbackTildeΓEquiv R S φ M (pullbackTildeΓUnit R S φ M m)
      = (1 : S) ⊗ₜ[R, φ.hom] m := by
  show (tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj M)).inv.hom
    (((moduleSpecΓFunctor (R := S)).map (pullbackTildeComponent R S φ M).hom).hom
      (pullbackTildeΓUnit R S φ M m)) = _
  have key : ((moduleSpecΓFunctor (R := S)).map (pullbackTildeComponent R S φ M).hom).hom
      (pullbackTildeΓUnit R S φ M m)
      = (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom
          ((1 : S) ⊗ₜ[R, φ.hom] m) := pullbackTildeIso_hom_app_unit_toOpen R S φ M m
  rw [key]
  exact tilde.isoTop_inv_toOpen _ _

/-- The inverse form of `pullbackTildeΓEquiv_unit`. -/
@[simp]
public theorem pullbackTildeΓEquiv_symm_one_tmul (m : M) :
    (pullbackTildeΓEquiv R S φ M).symm ((1 : S) ⊗ₜ[R, φ.hom] m)
      = pullbackTildeΓUnit R S φ M m :=
  (LinearEquiv.symm_apply_eq _).2 (pullbackTildeΓEquiv_unit R S φ M m).symm

/-- A scalar multiple of a canonical section corresponds to a general pure tensor.

Not a `simp` lemma: its left-hand side is not in simp-normal form, `map_smul` together with
`pullbackTildeΓEquiv_unit` already reducing it. -/
public theorem pullbackTildeΓEquiv_smul_unit (s : S) (m : M) :
    pullbackTildeΓEquiv R S φ M (s • pullbackTildeΓUnit R S φ M m)
      = s ⊗ₜ[R, φ.hom] m := by
  rw [map_smul, pullbackTildeΓEquiv_unit]
  exact (ModuleCat.ExtendScalars.smul_tmul φ.hom s 1 m).trans
    (congrArg (fun t : S ↦ t ⊗ₜ[R, φ.hom] m) (mul_one s))

/-- The inverse form of `pullbackTildeΓEquiv_smul_unit`: a general pure tensor corresponds to a
scalar multiple of a canonical section. -/
public theorem pullbackTildeΓEquiv_symm_tmul (s : S) (m : M) :
    (pullbackTildeΓEquiv R S φ M).symm (s ⊗ₜ[R, φ.hom] m)
      = s • pullbackTildeΓUnit R S φ M m :=
  (LinearEquiv.symm_apply_eq _).2 (pullbackTildeΓEquiv_smul_unit R S φ M s m).symm

/-- The canonical sections span all global sections of the pullback over `S`. With
`pullbackTildeΓEquiv_unit` this says that `pullbackTildeΓEquiv` is pinned down by its values on
the canonical sections. -/
public theorem span_range_pullbackTildeΓUnit :
    Submodule.span S (Set.range (pullbackTildeΓUnit R S φ M)) = ⊤ := by
  set P := Submodule.span (S : Type u) (Set.range (pullbackTildeΓUnit R S φ M)) with hP
  set Q := P.comap (pullbackTildeΓEquiv R S φ M).symm.toLinearMap with hQ
  have hbase (s : (S : Type u)) (m : M) :
      (pullbackTildeΓEquiv R S φ M).symm (s ⊗ₜ[R, φ.hom] m) ∈ P := by
    rw [pullbackTildeΓEquiv_symm_tmul, hP]
    exact Submodule.smul_mem _ s (Submodule.subset_span ⟨m, rfl⟩)
  have hmem (y : (ModuleCat.extendScalars φ.hom).obj M) : y ∈ Q := by
    induction y using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul a m => exact hbase a m
    | add y z hy hz => exact Submodule.add_mem _ hy hz
  refine eq_top_iff.2 fun x _ ↦ ?_
  simpa only [hQ, Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    using hmem (pullbackTildeΓEquiv R S φ M x)

/-- The affine pullback dictionary with the plain tensor product as its target: for an
`R`-algebra `S` and an `R`-module `M`, the global sections of the pullback of `M̃` along
`Spec (algebraMap R S)` are `S ⊗[R] M`, `S`-linearly. -/
public noncomputable def pullbackTildeΓTensorEquiv {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} (CommRingCat.of R)) :
    ((moduleSpecΓFunctor (R := CommRingCat.of S)).obj
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M)) : Type u)
      ≃ₗ[S] S ⊗[R] M :=
  (pullbackTildeΓEquiv (CommRingCat.of R) (CommRingCat.of S)
    (CommRingCat.ofHom (algebraMap R S)) M).trans (extendScalarsTensorEquiv M)

/-- **The normalization of `pullbackTildeΓTensorEquiv`.** It carries the canonical section
attached to `m` to the pure tensor `1 ⊗ m`. -/
@[simp]
public theorem pullbackTildeΓTensorEquiv_unit {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} (CommRingCat.of R)) (m : M) :
    pullbackTildeΓTensorEquiv (S := S) M
        (pullbackTildeΓUnit (CommRingCat.of R) (CommRingCat.of S)
          (CommRingCat.ofHom (algebraMap R S)) M m)
      = (1 : S) ⊗ₜ[R] m := by
  show extendScalarsTensorEquiv M
      (pullbackTildeΓEquiv (CommRingCat.of R) (CommRingCat.of S)
        (CommRingCat.ofHom (algebraMap R S)) M
        (pullbackTildeΓUnit (CommRingCat.of R) (CommRingCat.of S)
          (CommRingCat.ofHom (algebraMap R S)) M m)) = _
  rw [pullbackTildeΓEquiv_unit]
  exact extendScalarsTensorEquiv_tmul M 1 m

/-- The inverse form of `pullbackTildeΓTensorEquiv_unit`. -/
@[simp]
public theorem pullbackTildeΓTensorEquiv_symm_one_tmul {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} (CommRingCat.of R)) (m : M) :
    (pullbackTildeΓTensorEquiv (S := S) M).symm ((1 : S) ⊗ₜ[R] m)
      = pullbackTildeΓUnit (CommRingCat.of R) (CommRingCat.of S)
          (CommRingCat.ofHom (algebraMap R S)) M m :=
  (LinearEquiv.symm_apply_eq _).2 (pullbackTildeΓTensorEquiv_unit M m).symm

end AlgebraicGeometry
