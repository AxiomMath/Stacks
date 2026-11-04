module

public import StacksFrontier.Algebra.Module.Projective.Determinant.BaseChange
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.FreeRetract
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.StalkLinear
public import StacksFrontier.Topology.Sheaves.Stalk.Restrict
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a sheaf of modules which is locally associated to a module

Let `(X, 𝒪_X)` be a ringed space, `α : A → Γ(X, 𝒪_X)` a ring homomorphism, `M` an `A`-module and
`G` a sheaf of `𝒪_X`-modules *isomorphic* to the sheaf `ℱ_M` of construction (3) of Stacks 01BH.
This file reads clause (3) of that tag through the isomorphism: at every point `x`,

`G_x = 𝒪_{X,x} ⊗_A M`

as `𝒪_{X,x}`-modules. Combined with Stacks 08BL, which exhibits a flat sheaf of modules of finite
presentation as `ℱ_M` for a finite projective `M` on a neighbourhood of every point, this is the
base-change comparison that transports module-level computations over `𝒪_X(U)` to the stalk.

The computation this exists for is the rank idempotent of Stacks 0FJ9. The idempotent cutting out
the rank-`n` stratum of a finite projective module is an invariant of the module up to linear
equivalence and goes to the rank idempotent of a base change
(`ProjectiveDeterminant.rankIdempotent_eq_of_linearEquiv`,
`ProjectiveDeterminant.rankIdempotent_baseChange`), so the comparison above identifies the germ at
`x` of the rank idempotent of `M` with the rank idempotent of the stalk `G_x` over `𝒪_{X,x}`. That
identity is what makes a retract condition stated with the global idempotent `e_n ∈ 𝒪_X(U)`
testable on stalks.

## Main definitions

* `Stacks.AssociatedSheaf.stalkLinearEquivOfIso`: **the comparison**, `G_x ≅ 𝒪_{X,x} ⊗_A M` as an
  `𝒪_{X,x}`-linear equivalence, for any `G ≅ ℱ_M`.
* `Stacks.AssociatedSheaf.restrictStalkLinearEquiv`: the same for `F|_U ≅ ℱ_M` on an open `U` of a
  ringed space `W`, which is where Stacks 08BL supplies the isomorphism.
* `Stacks.AssociatedSheaf.valFunctor` and `Stacks.AssociatedSheaf.stalkModule`: a sheaf of
  `𝒪_X`-modules read as a presheaf of modules over `𝒪_X ⋙ forget₂ CommRingCat RingCat`, and the
  stalk of such a sheaf as an `𝒪_{X,x}`-module. These are the spellings at which instance search
  finds the `𝒪_{X,x}`-module structure on the stalk.
* `Stacks.AssociatedSheaf.restrictStalkCommRingIso` and
  `Stacks.AssociatedSheaf.restrictStalkAddEquiv`: the comparisons of the local ring and of the
  stalk of the module across restriction to an open, in the `CommRingCat` reading.

## Main results

* `Stacks.AssociatedSheaf.moduleFinite_stalkOfIso` and
  `Stacks.AssociatedSheaf.moduleProjective_stalkOfIso`: for `M` finite projective over `A`, the
  stalk `G_x` is finite projective over `𝒪_{X,x}`.
* `Stacks.AssociatedSheaf.germ_rankIdempotent_eq_rankIdempotent_stalk`: **the rank idempotent
  matches on stalks.** The image of `ProjectiveDeterminant.rankIdempotent A M n` under the
  structural map `A → 𝒪_{X,x}` is `ProjectiveDeterminant.rankIdempotent 𝒪_{X,x} G_x n`. Its form
  on an open `U` is `germ_rankIdempotent_eq_rankIdempotent_restrictStalk`.
* `Stacks.AssociatedSheaf.exists_open_stalkLinearEquiv_of_isFlat`: the comparison available where
  Stacks 08BL puts it — for a flat sheaf of modules of finite presentation, on a neighbourhood of
  every point of the ringed space.
* `Stacks.AssociatedSheaf.restrictStalkAddEquiv_germ_smul`: the germ-level semilinearity of the
  comparison across restriction to an open, over
  `Stacks.AssociatedSheaf.restrictStalkCommRingEquiv`.

## Implementation notes

*Why the comparison is needed at all.* The two retract conditions of the determinant argument of
Stacks 0FJN both reduce to the rank-idempotent identity above, and neither can be reached
sectionwise: `ℱ_N` is a sheafification, so `Γ(V, ℱ_N)` is not `𝒪_X(V) ⊗_A N` and the degreewise
annihilator has no sectionwise description. The stalk is where clause (3) of Stacks 01BH is an
equality on the nose, which is why the comparison is taken there.

*Which ambient ringed space.* The comparison is stated for a bare ringed space `X` and an
arbitrary `α : A → Γ(X, 𝒪_X)`, which is the generality construction (3) is defined in. Its form on
an open `U` of a ringed space `W` is that statement for `X := W.restrict U.isOpenEmbedding`, the
restricted ringed space on which `Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso_of_isFlat`
delivers 08BL. So `𝒪_x` there is the local ring read on `W|_U` and `F_x` the stalk of `F|_U`.

*What is still owed on the ambient space.* Identifying those with the local ring of `W` and the
stalk of `F` on `W` is a separate comparison, and the one the repository already has
(`Stacks.SheafOfModules.stalkRestrictIso`,
`AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso`) is stated over the stalk of the
structure sheaf taken in `RingCat`, whereas the tensor product here is formed over the stalk taken
in `CommRingCat` — a different colimit. The `CommRingCat` reading is built here as far as germs:
`restrictStalkCommRingIso`, `restrictStalkAddEquiv`, their germ descriptions, and the germ-level
semilinearity `restrictStalkAddEquiv_germ_smul`. Promoting that last one from germs to arbitrary
stalk elements, and hence to a linear equivalence over the ambient local ring, is *not* done: the
two spellings of the stalk of a module carry two `Module` instances which are definitionally equal
but not interchangeable by `rw`, Mathlib's
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier` and this
repository's `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, and instance search finds
neither of them at the restricted space's spelling of the point.

*Which spelling of the structure sheaf.* `Stacks.AssociatedSheaf.associatedSheafValFunctor` exists
because the `𝒪_{X,x}`-module structure on a stalk is found only for a presheaf of modules over
`𝒪_X ⋙ forget₂ CommRingCat RingCat`, and not through `structureSheafRing`: the latter is
`@[instance_reducible]` rather than `@[reducible]`, and only `@[reducible]` definitions are
unfolded when a goal is keyed into the discrimination tree instance search uses, so
`(structureSheafRing X).obj` is indexed as a projection and Mathlib's instance, keyed on a
functor composition, is never retrieved.
`Stacks.AssociatedSheaf.valFunctor` is the same device for an arbitrary
sheaf of `𝒪_X`-modules, and `associatedSheafValFunctor` factors through it
(`Stacks.AssociatedSheaf.associatedSheafValFunctor_eq`).

*No Stacks attribute.* Clause (3) of Stacks 01BH is already tagged, at
`Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv`; these are the transports of it that the
proof of Stacks 0FJN uses, not a statement of their own.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), clause (3).
* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Section 0FJ9](https://stacks.math.columbia.edu/tag/0FJ9)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.AssociatedSheaf

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (α : A →+* X.presheaf.obj (op ⊤)) (M : ModuleCat.{u} A)
  (G : SheafOfModules.{u} (structureSheafRing X)) (x : X.carrier)

/-! ### A sheaf of modules as a presheaf of modules at the spelling the stalk needs -/

/-- **A sheaf of `𝒪_X`-modules read as a presheaf of `𝒪_X`-modules**, with the presheaf of rings
spelled `𝒪_X ⋙ forget₂ CommRingCat RingCat` rather than
`structureSheafRing X`. The two presheaves of rings are the same; only the
first lets instance search find Mathlib's `𝒪_{X,x}`-module structure on the stalk. -/
def valFunctor : SheafOfModules.{u} (structureSheafRing X) ⥤
    PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  SheafOfModules.forget (structureSheafRing X) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)

/-- Construction (3) read at the spelling of `Stacks.AssociatedSheaf.valFunctor` is
`Stacks.AssociatedSheaf.associatedSheafValFunctor`. -/
theorem associatedSheafValFunctor_eq :
    associatedSheafValFunctor X α = associatedSheafFunctor.{u, u} X α ⋙ valFunctor X :=
  rfl

/-- The underlying presheaf of abelian groups is unchanged by
`Stacks.AssociatedSheaf.valFunctor`. -/
theorem valFunctor_obj_presheaf :
    ((valFunctor X).obj G).presheaf = G.val.presheaf :=
  rfl

/-- **The stalk at `x` of a sheaf of `𝒪_X`-modules, as an `𝒪_{X,x}`-module.** Its underlying type
is the stalk of the underlying presheaf of abelian groups
(`Stacks.AssociatedSheaf.stalkModule_eq`); naming it is what puts the `𝒪_{X,x}`-module structure
within reach of instance search, which does not find it through `G.val.presheaf`. -/
abbrev stalkModule : ModuleCat.{u} (X.presheaf.stalk x) :=
  (presheafStalkModuleFunctor X.presheaf x).obj ((valFunctor X).obj G)

/-- `Stacks.AssociatedSheaf.stalkModule` is the stalk of the underlying presheaf of abelian
groups. -/
theorem stalkModule_eq :
    ↥(stalkModule X G x) =
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) G.val.presheaf x) :=
  rfl

/-! ### The comparison -/

/-- **The stalk of a sheaf of modules isomorphic to `ℱ_M` is `𝒪_{X,x} ⊗_A M`.**

This is clause (3) of Stacks 01BH, `Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv`,
transported along the isomorphism: the stalk at `x` is a functor into `𝒪_{X,x}`-modules
(`Stacks.AssociatedSheaf.presheafStalkModuleFunctor`), so it carries the isomorphism `G ≅ ℱ_M` to
an `𝒪_{X,x}`-linear equivalence `G_x ≅ (ℱ_M)_x`. -/
def stalkLinearEquivOfIso (e : G ≅ associatedSheaf X α M) :
    letI := stalkAlgebra X α x
    stalkModule X G x ≃ₗ[X.presheaf.stalk x] (X.presheaf.stalk x ⊗[A] M) :=
  letI := stalkAlgebra X α x
  ((presheafStalkModuleFunctor X.presheaf x).mapIso ((valFunctor X).mapIso e) ≪≫
    (associatedSheafStalkFunctorIso X α x).symm.app M).toLinearEquiv

/-! ### Finiteness and projectivity of the stalk -/

variable [Module.Finite A M] [Module.Projective A M]

omit [Module.Projective A M] in
/-- The stalk of a sheaf of modules isomorphic to `ℱ_M` is a finite `𝒪_{X,x}`-module when `M` is a
finite `A`-module: finiteness passes to a base change, and the comparison
`Stacks.AssociatedSheaf.stalkLinearEquivOfIso` carries it to the stalk. -/
theorem moduleFinite_stalkOfIso (e : G ≅ associatedSheaf X α M) :
    letI := stalkAlgebra X α x
    Module.Finite (X.presheaf.stalk x) (stalkModule X G x) :=
  let := stalkAlgebra X α x
  Module.Finite.equiv (stalkLinearEquivOfIso X α M G x e).symm

omit [Module.Finite A M] in
/-- The stalk of a sheaf of modules isomorphic to `ℱ_M` is a projective `𝒪_{X,x}`-module when `M`
is a projective `A`-module: projectivity passes to a base change, and the comparison
`Stacks.AssociatedSheaf.stalkLinearEquivOfIso` carries it to the stalk. -/
theorem moduleProjective_stalkOfIso (e : G ≅ associatedSheaf X α M) :
    letI := stalkAlgebra X α x
    Module.Projective (X.presheaf.stalk x) (stalkModule X G x) :=
  let := stalkAlgebra X α x
  Module.Projective.of_equiv (stalkLinearEquivOfIso X α M G x e).symm

/-! ### The rank idempotent on stalks -/

/-- **The rank idempotent matches on stalks.** For `M` a finite projective `A`-module and
`G ≅ ℱ_M`, the image in `𝒪_{X,x}` of the idempotent cutting out the rank-`n` stratum of `M` is the
idempotent cutting out the rank-`n` stratum of the stalk `G_x` over `𝒪_{X,x}`.

The rank idempotent of a base change is the image of the rank idempotent
(`ProjectiveDeterminant.rankIdempotent_baseChange`) and the rank idempotent is unchanged by a
linear equivalence (`ProjectiveDeterminant.rankIdempotent_eq_of_linearEquiv`), so the comparison
`Stacks.AssociatedSheaf.stalkLinearEquivOfIso` identifies the two.

This is the identity that makes a condition stated with the global idempotent
`ProjectiveDeterminant.rankIdempotent A M n` of `𝒪_X(U)` testable on stalks, which is how the
determinant argument of Stacks 0FJN uses the local description of `F`. -/
theorem germ_rankIdempotent_eq_rankIdempotent_stalk (e : G ≅ associatedSheaf X α M) (n : ℕ) :
    letI := stalkAlgebra X α x
    letI := moduleFinite_stalkOfIso X α M G x e
    letI := moduleProjective_stalkOfIso X α M G x e
    algebraMap A (X.presheaf.stalk x) (ProjectiveDeterminant.rankIdempotent (R := A) (M := M) n) =
      ProjectiveDeterminant.rankIdempotent (R := X.presheaf.stalk x)
        (M := stalkModule X G x) n := by
  let := stalkAlgebra X α x
  let := moduleFinite_stalkOfIso X α M G x e
  let := moduleProjective_stalkOfIso X α M G x e
  refine (ProjectiveDeterminant.rankIdempotent_baseChange A (X.presheaf.stalk x) M n).trans ?_
  exact ProjectiveDeterminant.rankIdempotent_eq_of_linearEquiv _ _
    (stalkLinearEquivOfIso X α M G x e).symm n

/-! ### The comparison on a neighbourhood supplied by Stacks 08BL -/

section Open

variable {W : RingedSpace.{u, u}} (U : Opens W.carrier)
  (F : SheafOfModules.{u} (structureSheafRing W))

/-- **The restriction of a sheaf of `𝒪_W`-modules to an open `U`, read on the restricted ringed
space `W|_U`.** This is the ambient category of
`Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso_of_isFlat`, which is where Stacks 08BL
is available: construction (3) of Stacks 01BH needs a ringed space, so it cannot be written on
the slice site over `U`.

Naming it records that restricting the structure sheaf of rings and taking the structure sheaf
of rings of the restricted space agree: the `TopologicalSpace.Opens.sheafRestrict` of
`structureSheafRing W` and `structureSheafRing (W.restrict U.isOpenEmbedding)` are the same
sheaf of rings, since both are `𝒪_W` precomposed with `V ↦ U ∩ V` and postcomposed with
`forget₂ CommRingCat RingCat`. -/
abbrev restrictOver : SheafOfModules.{u}
    (structureSheafRing (W.restrict U.isOpenEmbedding)) :=
  (U.sheafOfModulesEquivOver (structureSheafRing W)).functor.obj (F.over U)

variable {x : W.carrier} (hU : x ∈ U)
  (M : ModuleCat.{u} ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)))

/-- **`F_x = 𝒪_x ⊗_{𝒪_W(U)} M` for `F` locally the sheaf associated to `M` on `U`.** The stalk
at a point of `U` of the restriction of `F` to `U` is the base change of `M` to the local ring
there, `𝒪_x` being the stalk of the structure sheaf of the restricted ringed space `W|_U` and
`𝒪_W(U)` its ring of global sections.

This is `Stacks.AssociatedSheaf.stalkLinearEquivOfIso` on the restricted ringed space; the
isomorphism it consumes is the one
`Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso_of_isFlat` produces from Stacks 08BL. -/
def restrictStalkLinearEquiv
    (e : restrictOver U F ≅ associatedSheaf (W.restrict U.isOpenEmbedding)
      (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M) :
    letI := stalkAlgebra (W.restrict U.isOpenEmbedding)
      (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)))
      (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)
    stalkModule (W.restrict U.isOpenEmbedding) (restrictOver U F)
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)
      ≃ₗ[(W.restrict U.isOpenEmbedding).presheaf.stalk
          (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)]
        ((W.restrict U.isOpenEmbedding).presheaf.stalk
          (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) ⊗[
            (W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)] M) :=
  stalkLinearEquivOfIso (W.restrict U.isOpenEmbedding)
    (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M (restrictOver U F)
    (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) e

/-- **The rank idempotent matches on the stalks of the restriction.** The germ at a point of `U`
of the idempotent cutting out the rank-`n` stratum of `M` is the idempotent cutting out the
rank-`n` stratum of the stalk of `F` there.

This is `Stacks.AssociatedSheaf.germ_rankIdempotent_eq_rankIdempotent_stalk` on the restricted
ringed space; over `W|_U` the structural map `𝒪_W(U) → 𝒪_x` is the germ map itself, `α` being the
identity. -/
theorem germ_rankIdempotent_eq_rankIdempotent_restrictStalk
    [Module.Finite ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M]
    [Module.Projective ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M]
    (e : restrictOver U F ≅ associatedSheaf (W.restrict U.isOpenEmbedding)
      (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M) (n : ℕ) :
    letI := stalkAlgebra (W.restrict U.isOpenEmbedding)
      (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)))
      (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)
    letI := moduleFinite_stalkOfIso (W.restrict U.isOpenEmbedding)
      (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M (restrictOver U F)
      (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) e
    letI := moduleProjective_stalkOfIso (W.restrict U.isOpenEmbedding)
      (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M (restrictOver U F)
      (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) e
    algebraMap ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))
        ((W.restrict U.isOpenEmbedding).presheaf.stalk
          (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier))
        (ProjectiveDeterminant.rankIdempotent
          (R := (W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) (M := M) n) =
      ProjectiveDeterminant.rankIdempotent
        (R := (W.restrict U.isOpenEmbedding).presheaf.stalk
          (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier))
        (M := stalkModule (W.restrict U.isOpenEmbedding) (restrictOver U F)
          (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)) n :=
  germ_rankIdempotent_eq_rankIdempotent_stalk (W.restrict U.isOpenEmbedding)
    (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M (restrictOver U F)
    (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) e n

end Open

section Flat

variable {W : RingedSpace.{u, u}} (F : SheafOfModules.{u} (structureSheafRing W))

/-- **`F_x = 𝒪_x ⊗_{𝒪_W(U)} M` on a neighbourhood of every point, for `F` flat and of finite
presentation.** Stacks 08BL gives a neighbourhood `U` of `x` and a finite projective
`𝒪_W(U)`-module `M` with `F|_U ≅ ℱ_M`
(`Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso_of_isFlat`), and
`Stacks.AssociatedSheaf.restrictStalkLinearEquiv` reads clause (3) of Stacks 01BH through that
isomorphism.

The rank-idempotent identity that goes with the comparison is
`Stacks.AssociatedSheaf.germ_rankIdempotent_eq_rankIdempotent_restrictStalk`, which needs the
finiteness and projectivity of `M` as instances and so is stated separately. -/
theorem exists_open_stalkLinearEquiv_of_isFlat [F.IsFinitePresentation]
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.sheaf) F)
    (x : W.carrier) :
    ∃ (U : Opens W.carrier) (hU : x ∈ U)
        (M : ModuleCat.{u} ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))),
      Module.Finite ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
        Module.Projective ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
        letI := stalkAlgebra (W.restrict U.isOpenEmbedding)
          (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)))
          (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)
        Nonempty (stalkModule (W.restrict U.isOpenEmbedding) (restrictOver U F)
              (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)
            ≃ₗ[(W.restrict U.isOpenEmbedding).presheaf.stalk
                (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)]
              ((W.restrict U.isOpenEmbedding).presheaf.stalk
                  (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) ⊗[
                (W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)] M)) := by
  obtain ⟨U, hU, M, hfin, hproj, ⟨e⟩⟩ := exists_open_associatedSheaf_iso_of_isFlat F hF x
  exact ⟨U, hU, M, hfin, hproj, ⟨restrictStalkLinearEquiv U F hU M e⟩⟩

end Flat

/-! ### Comparison with the stalk on the ambient ringed space -/

section Restrict

variable {W : RingedSpace.{u, u}} (U : Opens W.carrier)
  (F : SheafOfModules.{u} (structureSheafRing W)) {x : W.carrier} (hU : x ∈ U)

/-- `F` read as a presheaf of `𝒪_W`-modules, at the spelling
`Stacks.AssociatedSheaf.valFunctor` provides. -/
abbrev valOf : PresheafOfModules.{u} (W.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (valFunctor W).obj F

/-- The restriction of `F` to `U` read as a presheaf of `𝒪_{W|U}`-modules, at the spelling
`Stacks.AssociatedSheaf.valFunctor` provides. Its underlying presheaf of abelian groups is the
naive restriction of that of `F` (`Stacks.AssociatedSheaf.restrictValOf_presheaf`), which is what
makes Mathlib's comparison of stalks across restriction to an open apply to it. -/
abbrev restrictValOf : PresheafOfModules.{u}
    ((W.restrict U.isOpenEmbedding).presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (valFunctor (W.restrict U.isOpenEmbedding)).obj (restrictOver U F)

/-- The underlying presheaf of abelian groups of the restriction is the naive restriction `V ↦
F(U ∩ V)` of that of `F`. -/
theorem restrictValOf_presheaf :
    (restrictValOf U F).presheaf = (TopCat.Presheaf.imF U).op ⋙ (valOf F).presheaf :=
  rfl

/-- **The local ring of the restricted ringed space `W|_U` at a point of `U` is the local ring of
`W` there.** This is Mathlib's `AlgebraicGeometry.PresheafedSpace.restrictStalkIso` read in
`CommRingCat`.

The `RingCat` form of the same comparison is
`AlgebraicGeometry.RingedSpace.restrictModulesStalkRingIso`; `CommRingCat` is the reading needed
here, because the tensor product `𝒪_x ⊗_{𝒪_W(U)} M` is formed over the stalk taken in
`CommRingCat`, and the two stalks are colimits in different categories. -/
def restrictStalkCommRingIso :
    TopCat.Presheaf.stalk (C := CommRingCat.{u}) (W.restrict U.isOpenEmbedding).presheaf
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) ≅
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) W.presheaf x :=
  TopCat.Presheaf.stalkRestrictIso U W.presheaf
    (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)

/-- `Stacks.AssociatedSheaf.restrictStalkCommRingIso` as a ring equivalence. -/
def restrictStalkCommRingEquiv :
    ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (W.restrict U.isOpenEmbedding).presheaf
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)) ≃+*
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) W.presheaf x) :=
  (restrictStalkCommRingIso U hU).commRingCatIsoToRingEquiv

/-- On germs, the comparison of local rings sends the germ at a point of `U` of a section over
`V ⊆ U` to its germ as a section of `𝒪_W` over the image of `V`. -/
theorem restrictStalkCommRingEquiv_germ
    (V : Opens ((W.restrict U.isOpenEmbedding).carrier))
    (hz : (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) ∈ V)
    (r : ToType ((W.restrict U.isOpenEmbedding).presheaf.obj (op V))) :
    restrictStalkCommRingEquiv U hU
        ((W.restrict U.isOpenEmbedding).presheaf.germ V
          (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) hz r) =
      W.presheaf.germ ((TopCat.Presheaf.imF U).obj V) x
        ⟨(⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier), hz, rfl⟩ r := by
  have h := TopCat.Presheaf.stalkRestrictIso_germ U W.presheaf V
    (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) hz
  exact ConcreteCategory.congr_hom h r

/-- **The stalk at a point of `U` of the restriction of `F` to `U` is the stalk of `F` there**, as
an isomorphism of abelian groups. This is Mathlib's comparison of stalks across restriction to an
open, applicable because the underlying presheaf of abelian groups of the restriction is the naive
restriction (`Stacks.AssociatedSheaf.restrictValOf_presheaf`). -/
def restrictStalkAddEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (restrictValOf U F).presheaf
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)) ≃+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (valOf F).presheaf x) :=
  (TopCat.Presheaf.stalkRestrictIso U (valOf F).presheaf
    (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)).addCommGroupIsoToAddEquiv

/-- On germs, the comparison of stalks of modules sends the germ at a point of `U` of a section
over `V ⊆ U` to its germ as a section of `F` over the image of `V`. -/
theorem restrictStalkAddEquiv_germ
    (V : Opens ((W.restrict U.isOpenEmbedding).carrier))
    (hz : (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) ∈ V)
    (m : ToType ((restrictValOf U F).obj (op V))) :
    restrictStalkAddEquiv U F hU
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (restrictValOf U F).presheaf V
          (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) hz m) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (valOf F).presheaf
        ((TopCat.Presheaf.imF U).obj V) x
        ⟨(⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier), hz, rfl⟩ m := by
  have h := TopCat.Presheaf.stalkRestrictIso_germ U (valOf F).presheaf V
    (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) hz
  exact ConcreteCategory.congr_hom h m

/-- Semilinearity on germs: both comparisons turn a germ over `V` into the germ of the same
section over the image of `V`, so the identity to prove is `PresheafOfModules.germ_smul` for `F`
over that open of `W`. -/
theorem restrictStalkAddEquiv_germ_smul
    (V : Opens ((W.restrict U.isOpenEmbedding).carrier))
    (hz : (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) ∈ V)
    (r : ToType ((W.restrict U.isOpenEmbedding).presheaf.obj (op V)))
    (m : ToType ((restrictValOf U F).obj (op V))) :
    restrictStalkAddEquiv U F hU
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (restrictValOf U F).presheaf V
          (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) hz (r • m)) =
      restrictStalkCommRingEquiv U hU
          ((W.restrict U.isOpenEmbedding).presheaf.germ V
            (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) hz r) •
        restrictStalkAddEquiv U F hU
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (restrictValOf U F).presheaf V
            (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) hz m) := by
  rw [restrictStalkAddEquiv_germ, restrictStalkAddEquiv_germ, restrictStalkCommRingEquiv_germ]
  exact Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul W (valOf F) x
    ((TopCat.Presheaf.imF U).obj V)
    ⟨(⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier), hz, rfl⟩ r m

end Restrict

end Stacks.AssociatedSheaf

end

