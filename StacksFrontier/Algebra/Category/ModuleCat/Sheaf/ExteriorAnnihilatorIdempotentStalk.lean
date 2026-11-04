module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DeterminantIdempotentPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorStalk
public import StacksFrontier.Algebra.Module.Projective.Determinant.AnnihilatorIdempotent
import StacksCore.Tactic.StacksAttribute

/-!
# The two retract conditions of the determinant, tested on stalks

Let `(X, 𝒪_X)` be a ringed space, `F` a sheaf of `𝒪_X`-modules, `A` a package of the three
algebras of Section 17.21 for `F`, and `a` a section of `𝒪_X` over an open `W`. The determinant
argument of [Stacks, Tag 0FJN] presents `det(F)` by exhibiting each degreewise annihilator
`annₙ(F)` as a retract of `⋀ⁿ F` cut out by multiplication by a rank idempotent, and that needs
exactly two facts about `a`:

* multiplication by `a` carries every local section of `⋀ⁿ F` into `annₙ(F)`;
* multiplication by `a` is the identity on `annₙ(F)`.

Both are *stalk-local*: this file reduces them to the corresponding statements about the
germs of `a` acting on the exterior algebra of the stalks, where the two module-level facts
`ProjectiveDeterminant.rankIdempotent_smul_eq_zero_of_mem_exteriorPower` and
`ProjectiveDeterminant.rankIdempotent_smul_eq_self_of_mem_annihilatorPart` apply. It then
carries both across the restriction to the slice site over an open, which is the shape
`SheafOfModules.TensorExteriorSymmetricAlgebras.exists_isFinite_presentation_determinant_over`
consumes.

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras.smul_eq_zero_of_germ_smul_exteriorPower`: a
  section of `𝒪_X` whose germs annihilate the degree-`k` part of the exterior algebra of every
  stalk annihilates every local section of `⋀ᵏ F`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.isExteriorAnnihilated_smul`: **the first
  retract condition on a ringed space** — if the germs of `a` annihilate the degree-`(n+1)` part
  of the exterior algebra of every stalk, then `a • s` is exterior annihilated for every local
  section `s` of `⋀ⁿ F`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.smul_eq_self_of_isExteriorAnnihilated`: **the
  second retract condition on a ringed space** — if the germs of `a` are the identity on the
  degree-`n` annihilators in the stalks, then `a • s = s` for every exterior annihilated local
  section `s` of `⋀ⁿ F`.
* `germ_smul_exteriorPower_eq_zero_of_germ_eq_rankIdempotent` and
  `germ_smul_eq_self_of_germ_eq_rankIdempotent`, in the same namespace: those two stalk
  hypotheses hold for a section whose germ at each point is the rank idempotent of the stalk.
  These are the two module-level facts of Section 0FJ9 read on the stalks.
* `isExteriorAnnihilated_smul_of_germ_eq_rankIdempotent` and
  `smul_eq_self_of_germ_eq_rankIdempotent`, in the same namespace: the two conditions on a
  ringed space, with the stalk hypothesis in the form it is produced in.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.smul_mem_exteriorAnnihilator_over` and
  `smul_eq_self_of_mem_exteriorAnnihilator_over`: **the two conditions on the slice site over an
  open**, for an arbitrary package `B` of algebras for `F|_U` there; and
  `smul_mem_exteriorAnnihilator_over_of_germ_eq_rankIdempotent`,
  `smul_eq_self_of_mem_exteriorAnnihilator_over_of_germ_eq_rankIdempotent` with the
  rank-idempotent hypothesis.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.forall_smul_mem_exteriorAnnihilator_over` and
  `forall_smul_eq_self_of_mem_exteriorAnnihilator_over`: **the hypotheses `hmem` and `hself` of
  `exists_isFinite_presentation_determinant_over`**, in the literal shape that theorem states
  them in, for a compatible family `f` of sections of the structure sheaf.
* `exists_isFinite_presentation_determinant_over_of_germ_eq_rankIdempotent`, in the same
  namespace: **that theorem with both of them discharged** — the determinant of `F` over a
  trivialising open is finitely presented, granted the free retract, the finitely many nonzero
  degrees, and the rank-idempotent description of the germs of `f`.

## Implementation notes

**Why no open subspace appears.** The two conditions quantify over objects of the slice site
`Over U`, while the stalk comparison of Tag 01CH is written on the site of opens of a
topological space. The crossing is already available, and it is the *slice* crossing rather
than the open-subspace one:
`SheafOfModules.TensorExteriorSymmetricAlgebras.isExteriorAnnihilated_over` and
`isExteriorAnnihilated_of_over` carry the annihilation condition between `Over U` and the
ambient site in both directions, and the comparison `exteriorOverPieceIso` they are stated at is
an isomorphism, so the scalar multiplication and the equality of sections cross with it. So the
whole of this file lives on the ambient space `X`, and no comparison of `X` with the ringed
space `X|_U` is used.

**Why the degreewise membership needs no computation.** Every value of
`SheafOfModules.TensorExteriorSymmetricAlgebras.germWedge` in degree `k` lies in the degree-`k`
exterior power of the stalk by construction — it is the first component of a value of the
comparison `exteriorPowerStalkEquiv` of Tag 01CH, whose target is that submodule. So the first
condition does not need the multiplicativity `germWedge_wedgeGen` of the comparison: the
degree-`(n+1)` product whose vanishing is at stake is already a germ of a section of `⋀ⁿ⁺¹ F`,
and the hypothesis applies to it directly.

**Why the germ hypothesis is read at each object of the slice site and not only at `U`.** The two
conditions are quantified over all objects `V` of `Over U`, and the scalar there is the value
`f n` takes at `V`, so the hypothesis is stated for that value over the open `V.left`. For a
compatible family `f` it is enough to know it over `U`: the value at `V` is the restriction of
the value at the terminal object `Over.mk (𝟙 U)` by the compatibility of a
`CategoryTheory.Functor.sections`, and a germ is unchanged by restriction
(`TopCat.Presheaf.germ_res_apply`). That reduction is left to the caller, which is where the
family `f` is built.

**What is not proved here.** The hypothesis of the `rankIdempotent` forms — that the germ at `x`
of the scalar is the rank idempotent of the stalk `F_x` over `𝒪_{X,x}` — is not established
here. On a flat sheaf of modules of finite presentation it comes from Tag 08BL through
`Stacks.AssociatedSheaf.germ_rankIdempotent_eq_rankIdempotent_restrictStalk`, which states it
for the stalks of the *restricted* ringed space `X|_U`; identifying those with the stalks of `X`
is the comparison recorded as missing in the implementation notes of
`StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.StalkBaseChange`. The finiteness and
projectivity of the stalks come from the same place, through
`Stacks.AssociatedSheaf.moduleFinite_stalkOfIso` and `moduleProjective_stalkOfIso`.

**No `@[stacks 0FJN]` attribute.** These are the two retract conditions that the proof of that
tag consumes, not a statement of the tag.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe u

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

/-! ### The two conditions on a ringed space -/

section RingedSpace

variable {X : TopCat.{u}}
  {Osharp : Sheaf (Opens.grothendieckTopology (X : Type u)) CommRingCat.{u}}
  {F : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp)}
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology (X : Type u)) F)

/-- **A section of the structure sheaf whose germs annihilate the degree-`k` part of the
exterior algebra of every stalk annihilates every local section of `⋀ᵏ F`.** Vanishing of a
section of a sheaf of modules is tested on germs, and the germ of `a • w` read through the
comparison of Tag 01CH is the germ of `a` acting on an element of the degree-`k` exterior power
of the stalk. -/
theorem smul_eq_zero_of_germ_smul_exteriorPower (k : ℕ) {W : Opens (X : Type u)}
    (a : ToType ((toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp).obj.obj (op W)))
    (ha : ∀ (y : (X : Type u)) (hy : y ∈ W)
      (z : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y))),
      z ∈ ⋀[ToType (TopCat.Presheaf.stalk Osharp.obj y)]^k
          (ToType (TopCat.Presheaf.stalk F.val.presheaf y)) →
        TopCat.Presheaf.germ Osharp.obj W y hy a • z = 0)
    (w : ToType ((A.exteriorPower k).val.obj (op W))) :
    a • w = 0 := by
  refine TopCat.Presheaf.section_ext
    ((_root_.SheafOfModules.toSheaf
      (toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp)).obj
        (A.exteriorPower k)) W (a • w) 0 fun y hy => ?_
  refine Eq.trans (A.germ_eq_zero_of_germWedge_eq_zero y k hy (a • w) ?_)
    (Stacks.SheafOfModules.germ_zero (M := A.exteriorPower k) y hy).symm
  rw [A.germWedge_smul y k hy a w]
  exact ha y hy (A.germWedge y k hy w)
    (A.exteriorPowerStalkEquiv k y (Stacks.SheafOfModules.germ (A.exteriorPower k) y hy w)).2

/-- **The first retract condition of Tag 0FJN on a ringed space.** If the germs of `a` annihilate
the degree-`(n+1)` part of the exterior algebra of every stalk over `W`, then `a • s` is exterior
annihilated for every local section `s` of `⋀ⁿ F` over `W`.

The annihilation condition is the vanishing of a product of `a • s` with a degree-one section
over an arbitrary smaller open; the scalar comes out of both the restriction and the
multiplication, and what is left is a section of `⋀ⁿ⁺¹ F` multiplied by a restriction of `a`,
to which `smul_eq_zero_of_germ_smul_exteriorPower` applies. -/
theorem isExteriorAnnihilated_smul (n : ℕ) {W : Opens (X : Type u)}
    (a : ToType ((toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp).obj.obj (op W)))
    (ha : ∀ (y : (X : Type u)) (hy : y ∈ W)
      (z : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y))),
      z ∈ ⋀[ToType (TopCat.Presheaf.stalk Osharp.obj y)]^(n + 1)
          (ToType (TopCat.Presheaf.stalk F.val.presheaf y)) →
        TopCat.Presheaf.germ Osharp.obj W y hy a • z = 0)
    (s : ToType ((A.exteriorPower n).val.obj (op W))) :
    A.IsExteriorAnnihilated n (a • s) := by
  intro V f m
  have hVW : V.unop ≤ W := f.unop.le
  have hf : f = (homOfLE hVW).op := Subsingleton.elim _ _
  rw [map_smulₛₗ ((A.exteriorPower n).val.restrictₛₗ f) a s]
  refine (A.wedgeGen_eq_zero_iff n V m _).mp ?_
  rw [wedgeGen_smul_right]
  refine A.smul_eq_zero_of_germ_smul_exteriorPower (n + 1) _ (fun y hy z hz => ?_) _
  have hgerm : TopCat.Presheaf.germ Osharp.obj (unop V) y hy
      ((toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp).obj.map f a) =
      TopCat.Presheaf.germ Osharp.obj W y (hVW hy) a := by
    rw [hf]
    exact TopCat.Presheaf.germ_res_apply Osharp.obj (homOfLE hVW) y hy a
  rw [hgerm]
  exact ha y (hVW hy) z hz

/-- **The second retract condition of Tag 0FJN on a ringed space.** If the germs of `a` are the
identity on the degree-`n` annihilators in the stalks, then `a • s = s` for every exterior
annihilated local section `s` of `⋀ⁿ F`.

Two sections of a sheaf of modules with the same germs are equal, the comparison of Tag 01CH is
injective on stalks, and the germ of an exterior annihilated section is killed by every
degree-one element of the exterior algebra of the stalk
(`mul_germWedge_eq_zero_of_isExteriorAnnihilated`), which is the hypothesis the stalk condition
is read at. -/
theorem smul_eq_self_of_isExteriorAnnihilated (n : ℕ) {W : Opens (X : Type u)}
    (a : ToType ((toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp).obj.obj (op W)))
    (ha : ∀ (y : (X : Type u)) (hy : y ∈ W)
      (v : ⋀[ToType (TopCat.Presheaf.stalk Osharp.obj y)]^n
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y))),
      (∀ μ : ToType (TopCat.Presheaf.stalk F.val.presheaf y),
          ExteriorAlgebra.ι (ToType (TopCat.Presheaf.stalk Osharp.obj y)) μ *
            (v : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
              (ToType (TopCat.Presheaf.stalk F.val.presheaf y))) = 0) →
        TopCat.Presheaf.germ Osharp.obj W y hy a •
            (v : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
              (ToType (TopCat.Presheaf.stalk F.val.presheaf y))) = v)
    (s : ToType ((A.exteriorPower n).val.obj (op W)))
    (hs : A.IsExteriorAnnihilated n s) :
    a • s = s := by
  refine TopCat.Presheaf.section_ext
    ((_root_.SheafOfModules.toSheaf
      (toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp)).obj
        (A.exteriorPower n)) W (a • s) s fun y hy => ?_
  refine A.germ_eq_of_germWedge_eq y n hy hy (a • s) s ?_
  rw [A.germWedge_smul y n hy a s]
  exact ha y hy (A.exteriorPowerStalkEquiv n y
      (Stacks.SheafOfModules.germ (A.exteriorPower n) y hy s))
    fun μ => A.mul_germWedge_eq_zero_of_isExteriorAnnihilated y n hy s hs μ

end RingedSpace

/-! ### The stalk hypotheses from the rank idempotents -/

section RankIdempotent

variable {X : TopCat.{u}}
  {Osharp : Sheaf (Opens.grothendieckTopology (X : Type u)) CommRingCat.{u}}
  (F : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp))
  {W : Opens (X : Type u)}
  (a : ToType ((toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp).obj.obj (op W)))
  (hfin : ∀ (y : (X : Type u)), y ∈ W →
    Module.Finite (ToType (TopCat.Presheaf.stalk Osharp.obj y))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
  (hproj : ∀ (y : (X : Type u)), y ∈ W →
    Module.Projective (ToType (TopCat.Presheaf.stalk Osharp.obj y))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))

/-- **The rank-`n` idempotent of the stalk annihilates the degree-`(n+1)` part of the exterior
algebra of the stalk**, which is the stalk hypothesis of `isExteriorAnnihilated_smul`, for a
section of `𝒪_X` whose germ at each point of `W` is that idempotent. This is
`ProjectiveDeterminant.rankIdempotent_smul_eq_zero_of_mem_exteriorPower` read on the stalks. -/
theorem germ_smul_exteriorPower_eq_zero_of_germ_eq_rankIdempotent (n : ℕ)
    (hidem : ∀ (y : (X : Type u)) (hy : y ∈ W),
      letI := hfin y hy
      letI := hproj y hy
      TopCat.Presheaf.germ Osharp.obj W y hy a =
        ProjectiveDeterminant.rankIdempotent
          (R := ToType (TopCat.Presheaf.stalk Osharp.obj y))
          (M := ToType (TopCat.Presheaf.stalk F.val.presheaf y)) n)
    (y : (X : Type u)) (hy : y ∈ W)
    (z : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
    (hz : z ∈ ⋀[ToType (TopCat.Presheaf.stalk Osharp.obj y)]^(n + 1)
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y))) :
    TopCat.Presheaf.germ Osharp.obj W y hy a • z = 0 := by
  let := hfin y hy
  let := hproj y hy
  rw [hidem y hy]
  exact ProjectiveDeterminant.rankIdempotent_smul_eq_zero_of_mem_exteriorPower
    (Nat.lt_succ_self n) hz

/-- **The rank-`n` idempotent of the stalk is the identity on the degree-`n` annihilator in the
stalk**, which is the stalk hypothesis of `smul_eq_self_of_isExteriorAnnihilated`, for a section
of `𝒪_X` whose germ at each point of `W` is that idempotent. This is
`ProjectiveDeterminant.rankIdempotent_smul_eq_self_of_mem_annihilatorPart` read on the stalks. -/
theorem germ_smul_eq_self_of_germ_eq_rankIdempotent (n : ℕ)
    (hidem : ∀ (y : (X : Type u)) (hy : y ∈ W),
      letI := hfin y hy
      letI := hproj y hy
      TopCat.Presheaf.germ Osharp.obj W y hy a =
        ProjectiveDeterminant.rankIdempotent
          (R := ToType (TopCat.Presheaf.stalk Osharp.obj y))
          (M := ToType (TopCat.Presheaf.stalk F.val.presheaf y)) n)
    (y : (X : Type u)) (hy : y ∈ W)
    (v : ⋀[ToType (TopCat.Presheaf.stalk Osharp.obj y)]^n
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
    (hv : ∀ μ : ToType (TopCat.Presheaf.stalk F.val.presheaf y),
      ExteriorAlgebra.ι (ToType (TopCat.Presheaf.stalk Osharp.obj y)) μ *
        (v : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
          (ToType (TopCat.Presheaf.stalk F.val.presheaf y))) = 0) :
    TopCat.Presheaf.germ Osharp.obj W y hy a •
        (v : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
          (ToType (TopCat.Presheaf.stalk F.val.presheaf y))) = v := by
  let := hfin y hy
  let := hproj y hy
  rw [hidem y hy]
  exact ProjectiveDeterminant.rankIdempotent_smul_eq_self_of_mem_annihilatorPart
    ((Stacks.ExteriorAnnihilator.mem_part_iff v).mpr hv)

end RankIdempotent

/-! ### The two conditions on a ringed space, from the rank idempotents -/

section RingedSpaceRankIdempotent

variable {X : TopCat.{u}}
  {Osharp : Sheaf (Opens.grothendieckTopology (X : Type u)) CommRingCat.{u}}
  {F : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp)}
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology (X : Type u)) F)

/-- **The first retract condition on a ringed space, with the stalk hypothesis in the form it is
produced in**: the germ of `a` at each point of `W` is the rank-`n` idempotent of the stalk. -/
theorem isExteriorAnnihilated_smul_of_germ_eq_rankIdempotent (n : ℕ) {W : Opens (X : Type u)}
    (a : ToType ((toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp).obj.obj (op W)))
    (hfin : ∀ (y : (X : Type u)), y ∈ W →
      Module.Finite (ToType (TopCat.Presheaf.stalk Osharp.obj y))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
    (hproj : ∀ (y : (X : Type u)), y ∈ W →
      Module.Projective (ToType (TopCat.Presheaf.stalk Osharp.obj y))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
    (hidem : ∀ (y : (X : Type u)) (hy : y ∈ W),
      letI := hfin y hy
      letI := hproj y hy
      TopCat.Presheaf.germ Osharp.obj W y hy a =
        ProjectiveDeterminant.rankIdempotent
          (R := ToType (TopCat.Presheaf.stalk Osharp.obj y))
          (M := ToType (TopCat.Presheaf.stalk F.val.presheaf y)) n)
    (s : ToType ((A.exteriorPower n).val.obj (op W))) :
    A.IsExteriorAnnihilated n (a • s) :=
  A.isExteriorAnnihilated_smul n a
    (germ_smul_exteriorPower_eq_zero_of_germ_eq_rankIdempotent F a hfin hproj n hidem) s

/-- **The second retract condition on a ringed space, with the stalk hypothesis in the form it is
produced in**: the germ of `a` at each point of `W` is the rank-`n` idempotent of the stalk. -/
theorem smul_eq_self_of_germ_eq_rankIdempotent (n : ℕ) {W : Opens (X : Type u)}
    (a : ToType ((toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp).obj.obj (op W)))
    (hfin : ∀ (y : (X : Type u)), y ∈ W →
      Module.Finite (ToType (TopCat.Presheaf.stalk Osharp.obj y))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
    (hproj : ∀ (y : (X : Type u)), y ∈ W →
      Module.Projective (ToType (TopCat.Presheaf.stalk Osharp.obj y))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
    (hidem : ∀ (y : (X : Type u)) (hy : y ∈ W),
      letI := hfin y hy
      letI := hproj y hy
      TopCat.Presheaf.germ Osharp.obj W y hy a =
        ProjectiveDeterminant.rankIdempotent
          (R := ToType (TopCat.Presheaf.stalk Osharp.obj y))
          (M := ToType (TopCat.Presheaf.stalk F.val.presheaf y)) n)
    (s : ToType ((A.exteriorPower n).val.obj (op W)))
    (hs : A.IsExteriorAnnihilated n s) :
    a • s = s :=
  A.smul_eq_self_of_isExteriorAnnihilated n a
    (germ_smul_eq_self_of_germ_eq_rankIdempotent F a hfin hproj n hidem) s hs

end RingedSpaceRankIdempotent

/-! ### The two conditions on the slice site over an open -/

section Over

variable {X : TopCat.{u}}
  {Osharp : Sheaf (Opens.grothendieckTopology (X : Type u)) CommRingCat.{u}}
  {F : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp)}
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology (X : Type u)) F)
  (U : Opens (X : Type u))
  [((Opens.grothendieckTopology (X : Type u)).over U).HasSheafCompose
    (forget₂ CommRingCat.{u} RingCat.{u})]
  [((Opens.grothendieckTopology (X : Type u)).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify ((Opens.grothendieckTopology (X : Type u)).over U) AddCommGrpCat.{u}]
  (B : TensorExteriorSymmetricAlgebras (Osharp := Osharp.over U)
    ((Opens.grothendieckTopology (X : Type u)).over U) (F.over U))

/-- The comparison `exteriorOverPieceIso` is linear: its forward map undoes scalar multiplication
after its inverse. The scalar `a'` is the ambient spelling of the slice scalar `a`. -/
private theorem exteriorOverPieceIso_hom_smul_inv (n : ℕ) (V : (Over U)ᵒᵖ)
    (a : ToType ((toRingCat ((Opens.grothendieckTopology (X : Type u)).over U)
      (Osharp.over U)).obj.obj V))
    (a' : ToType (((toRingCat (Opens.grothendieckTopology (X : Type u))
      Osharp).over U).obj.obj V)) (ha : a' = a)
    (x : ToType ((B.exteriorPower n).val.obj V)) :
    (exteriorOverPieceIso A U B (n : ℤ)).hom.val.app V
      (a' • (exteriorOverPieceIso A U B (n : ℤ)).inv.val.app V x) = a • x := by
  subst ha
  have hsm := map_smul ((exteriorOverPieceIso A U B (n : ℤ)).hom.val.app V).hom a'
    ((exteriorOverPieceIso A U B (n : ℤ)).inv.val.app V x)
  rwa [exteriorOverPieceIso_hom_inv A U B (n : ℤ) V x] at hsm

include A in
/-- **The first retract condition of Tag 0FJN on the slice site over `U`**, which is the
hypothesis `hmem` of
`SheafOfModules.TensorExteriorSymmetricAlgebras.exists_isFinite_presentation_determinant_over`.

The section `x` is the comparison `exteriorOverPieceIso` applied to a section of `⋀ⁿ F` over
`V.left`, the comparison is linear so the scalar passes through it, and
`isExteriorAnnihilated_over` carries the ambient annihilation condition — which is
`isExteriorAnnihilated_smul` — to the slice site.

The ambient package `A` does not occur in the statement; it is the package the determinant whose
presentation is at stake is formed from, and it is what makes the comparison with the slice site
available.

The scalar is written out at the ambient spelling `(toRingCat J O♯).obj.obj (op V.left)` wherever
it multiplies an ambient section: the slice spelling and the ambient one are definitionally equal
but instance search does not cross between them, so a bare `a • ·` there fails to find `HSMul`. -/
theorem smul_mem_exteriorAnnihilator_over (n : ℕ) (V : (Over U)ᵒᵖ)
    (a : ToType ((toRingCat ((Opens.grothendieckTopology (X : Type u)).over U)
      (Osharp.over U)).obj.obj V))
    (ha : ∀ (y : (X : Type u)) (hy : y ∈ (unop V).left)
      (z : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y))),
      z ∈ ⋀[ToType (TopCat.Presheaf.stalk Osharp.obj y)]^(n + 1)
          (ToType (TopCat.Presheaf.stalk F.val.presheaf y)) →
        TopCat.Presheaf.germ Osharp.obj (unop V).left y hy a • z = 0)
    (x : ToType ((B.exteriorPower n).val.obj V)) :
    a • x ∈ (B.exteriorAnnihilator n).obj V := by
  obtain ⟨a, rfl⟩ : ∃ a₀ : ToType (((toRingCat (Opens.grothendieckTopology (X : Type u))
      Osharp).over U).obj.obj V), a₀ = a := ⟨a, rfl⟩
  refine (mem_exteriorAnnihilator_obj B n _).mpr ?_
  have key := isExteriorAnnihilated_over A U B n (V := V)
    (a • (exteriorOverPieceIso A U B (n : ℤ)).inv.val.app V x)
    (A.isExteriorAnnihilated_smul n a ha
      ((exteriorOverPieceIso A U B (n : ℤ)).inv.val.app V x))
  rwa [exteriorOverPieceIso_hom_smul_inv A U B n V a a rfl x] at key

include A in
/-- **The second retract condition of Tag 0FJN on the slice site over `U`**, which is the
hypothesis `hself` of
`SheafOfModules.TensorExteriorSymmetricAlgebras.exists_isFinite_presentation_determinant_over`.

Here the annihilation hypothesis crosses the other way, by `isExteriorAnnihilated_of_over`, and
the equality of sections is pushed back along the comparison, which is injective on sections
because it is an isomorphism. -/
theorem smul_eq_self_of_mem_exteriorAnnihilator_over (n : ℕ) (V : (Over U)ᵒᵖ)
    (a : ToType ((toRingCat ((Opens.grothendieckTopology (X : Type u)).over U)
      (Osharp.over U)).obj.obj V))
    (ha : ∀ (y : (X : Type u)) (hy : y ∈ (unop V).left)
      (v : ⋀[ToType (TopCat.Presheaf.stalk Osharp.obj y)]^n
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y))),
      (∀ μ : ToType (TopCat.Presheaf.stalk F.val.presheaf y),
          ExteriorAlgebra.ι (ToType (TopCat.Presheaf.stalk Osharp.obj y)) μ *
            (v : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
              (ToType (TopCat.Presheaf.stalk F.val.presheaf y))) = 0) →
        TopCat.Presheaf.germ Osharp.obj (unop V).left y hy a •
            (v : ExteriorAlgebra (ToType (TopCat.Presheaf.stalk Osharp.obj y))
              (ToType (TopCat.Presheaf.stalk F.val.presheaf y))) = v)
    (y : (B.exteriorAnnihilator n).obj V) :
    a • (y : ToType ((B.exteriorPower n).val.obj V)) =
      (y : ToType ((B.exteriorPower n).val.obj V)) := by
  obtain ⟨a, rfl⟩ : ∃ a₀ : ToType (((toRingCat (Opens.grothendieckTopology (X : Type u))
      Osharp).over U).obj.obj V), a₀ = a := ⟨a, rfl⟩
  have hann : A.IsExteriorAnnihilated n
      ((exteriorOverPieceIso A U B (n : ℤ)).inv.val.app V
        (y : ToType ((B.exteriorPower n).val.obj V))) :=
    isExteriorAnnihilated_of_over A U B n _ ((mem_exteriorAnnihilator_obj B n _).mp y.2)
  have key := A.smul_eq_self_of_isExteriorAnnihilated n a ha
    ((exteriorOverPieceIso A U B (n : ℤ)).inv.val.app V
      (y : ToType ((B.exteriorPower n).val.obj V))) hann
  refine (exteriorOverPieceIso_hom_smul_inv A U B n V a a rfl _).symm.trans (Eq.trans (congrArg
    ((exteriorOverPieceIso A U B (n : ℤ)).hom.val.app V) key) ?_)
  exact exteriorOverPieceIso_hom_inv A U B (n : ℤ) V _

/-! #### With the stalk hypothesis in the form it is produced in -/

section RankIdempotent

variable (n : ℕ) (V : (Over U)ᵒᵖ)
  (a : ToType ((toRingCat ((Opens.grothendieckTopology (X : Type u)).over U)
    (Osharp.over U)).obj.obj V))
  (hfin : ∀ (y : (X : Type u)), y ∈ (unop V).left →
    Module.Finite (ToType (TopCat.Presheaf.stalk Osharp.obj y))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
  (hproj : ∀ (y : (X : Type u)), y ∈ (unop V).left →
    Module.Projective (ToType (TopCat.Presheaf.stalk Osharp.obj y))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
  (hidem : ∀ (y : (X : Type u)) (hy : y ∈ (unop V).left),
    letI := hfin y hy
    letI := hproj y hy
    TopCat.Presheaf.germ Osharp.obj (unop V).left y hy a =
      ProjectiveDeterminant.rankIdempotent
        (R := ToType (TopCat.Presheaf.stalk Osharp.obj y))
        (M := ToType (TopCat.Presheaf.stalk F.val.presheaf y)) n)

include A hfin hproj hidem in
/-- **`hmem` of `exists_isFinite_presentation_determinant_over`, with the stalk hypothesis in the
form it is produced in**: the germ of the scalar at each point of `V.left` is the rank-`n`
idempotent of the stalk of `F` there. -/
theorem smul_mem_exteriorAnnihilator_over_of_germ_eq_rankIdempotent
    (x : ToType ((B.exteriorPower n).val.obj V)) :
    a • x ∈ (B.exteriorAnnihilator n).obj V :=
  smul_mem_exteriorAnnihilator_over A U B n V a
    (germ_smul_exteriorPower_eq_zero_of_germ_eq_rankIdempotent F a hfin hproj n hidem) x

include A hfin hproj hidem in
/-- **`hself` of `exists_isFinite_presentation_determinant_over`, with the stalk hypothesis in the
form it is produced in**: the germ of the scalar at each point of `V.left` is the rank-`n`
idempotent of the stalk of `F` there. -/
theorem smul_eq_self_of_mem_exteriorAnnihilator_over_of_germ_eq_rankIdempotent
    (y : (B.exteriorAnnihilator n).obj V) :
    a • (y : ToType ((B.exteriorPower n).val.obj V)) =
      (y : ToType ((B.exteriorPower n).val.obj V)) :=
  smul_eq_self_of_mem_exteriorAnnihilator_over A U B n V a
    (germ_smul_eq_self_of_germ_eq_rankIdempotent F a hfin hproj n hidem) y

end RankIdempotent

/-! #### The two conditions as `exists_isFinite_presentation_determinant_over` states them -/

section Sections

variable (f : ℕ → ((toRingCat ((Opens.grothendieckTopology (X : Type u)).over U)
    (Osharp.over U)).obj ⋙ CategoryTheory.forget RingCat).sections)
  (hfin : ∀ (V : (Over U)ᵒᵖ) (y : (X : Type u)), y ∈ (unop V).left →
    Module.Finite (ToType (TopCat.Presheaf.stalk Osharp.obj y))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
  (hproj : ∀ (V : (Over U)ᵒᵖ) (y : (X : Type u)), y ∈ (unop V).left →
    Module.Projective (ToType (TopCat.Presheaf.stalk Osharp.obj y))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y)))
  (hidem : ∀ (n : ℕ) (V : (Over U)ᵒᵖ) (y : (X : Type u)) (hy : y ∈ (unop V).left),
    letI := hfin V y hy
    letI := hproj V y hy
    TopCat.Presheaf.germ Osharp.obj (unop V).left y hy ((f n).val V) =
      ProjectiveDeterminant.rankIdempotent
        (R := ToType (TopCat.Presheaf.stalk Osharp.obj y))
        (M := ToType (TopCat.Presheaf.stalk F.val.presheaf y)) n)

include A hfin hproj hidem in
/-- **The hypothesis `hmem` of
`SheafOfModules.TensorExteriorSymmetricAlgebras.exists_isFinite_presentation_determinant_over`,
in the literal shape that theorem states it in**, for a compatible family `f` of sections of the
structure sheaf whose germs are the rank idempotents of the stalks of `F`. -/
theorem forall_smul_mem_exteriorAnnihilator_over :
    ∀ (n : ℕ) (V : (Over U)ᵒᵖ) (x : ToType ((B.exteriorPower n).val.obj V)),
      (f n).val V • x ∈ (B.exteriorAnnihilator n).obj V :=
  fun n V x => smul_mem_exteriorAnnihilator_over_of_germ_eq_rankIdempotent A U B n V
    ((f n).val V) (hfin V) (hproj V) (hidem n V) x

include A hfin hproj hidem in
/-- **The hypothesis `hself` of
`SheafOfModules.TensorExteriorSymmetricAlgebras.exists_isFinite_presentation_determinant_over`,
in the literal shape that theorem states it in**, for a compatible family `f` of sections of the
structure sheaf whose germs are the rank idempotents of the stalks of `F`. -/
theorem forall_smul_eq_self_of_mem_exteriorAnnihilator_over :
    ∀ (n : ℕ) (V : (Over U)ᵒᵖ) (y : (B.exteriorAnnihilator n).obj V),
      (f n).val V • (y : ToType ((B.exteriorPower n).val.obj V)) =
        (y : ToType ((B.exteriorPower n).val.obj V)) :=
  fun n V y => smul_eq_self_of_mem_exteriorAnnihilator_over_of_germ_eq_rankIdempotent A U B n V
    ((f n).val V) (hfin V) (hproj V) (hidem n V) y

include A hfin hproj hidem in
/-- **The determinant of `F` restricted to a trivialising open has a finite presentation, granted
the rank-idempotent description of the germs.** This is
`SheafOfModules.TensorExteriorSymmetricAlgebras.exists_isFinite_presentation_determinant_over`
with its two stalk-local retract hypotheses discharged: what is left to supply is the free
retract of `F|_U`, the finitely many degrees in which the annihilator is nonzero, and the
identification of the germs of `f` with the rank idempotents of the stalks. -/
theorem exists_isFinite_presentation_determinant_over_of_germ_eq_rankIdempotent
    [HasSheafify ((Opens.grothendieckTopology (X : Type u)).over U) AddCommGrpCat.{u}]
    {ι : Type u} [Finite ι]
    (B' : TensorExteriorSymmetricAlgebras (Osharp := Osharp.over U)
      ((Opens.grothendieckTopology (X : Type u)).over U)
      (_root_.SheafOfModules.free
        (R := toRingCat ((Opens.grothendieckTopology (X : Type u)).over U) (Osharp.over U)) ι))
    (ρ : Retract (F.over U) (_root_.SheafOfModules.free
      (R := toRingCat ((Opens.grothendieckTopology (X : Type u)).over U) (Osharp.over U)) ι))
    (s : Finset ℕ)
    (hz : ∀ n ∉ s, IsZero (B.exteriorAnnihilator n).toSheafOfModules) :
    ∃ p : ((A.determinant).over U).Presentation, p.IsFinite :=
  exists_isFinite_presentation_determinant_over A U B B' ρ f s hz
    (forall_smul_mem_exteriorAnnihilator_over A U B f hfin hproj hidem)
    (forall_smul_eq_self_of_mem_exteriorAnnihilator_over A U B f hfin hproj hidem)

end Sections

end Over

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
