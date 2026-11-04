module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to a slice site commutes with the symmetric and exterior powers

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it, `M` a sheaf of modules over the
underlying sheaf of rings, and `U : C`. This file proves

`(Symⁿ M)|_U ≅ Symⁿ(M|_U)` and `(⋀ⁿ M)|_U ≅ ⋀ⁿ(M|_U)`,

where `|_U` is restriction to the slice site `(Over U, J.over U)`
(`SheafOfModules.over`) and the two sides are the degree-`n` pieces of *any* symmetric,
respectively exterior, algebra of `M` over `(C, J)` and of `M|_U` over `(Over U, J.over U)`.
This is the restriction-to-an-open-immersion analogue of
`Stacks.PullbackAlgebra.pullbackTensorPieceIso`, which does the tensor case for a pullback
along a morphism of ringed spaces.

## The proof, and why it needs no new mathematics

Tag 01CG says the degree-`n` symmetric power of `M` is the sheafification of the presheaf
`V ↦ Symⁿ_{O♯(V)}(M(V))`, and `SheafOfModules.symmetricPieceIso` already names the resulting
degreewise isomorphism between an arbitrary symmetric algebra of `M` and the sheafified
sectionwise one. So the comparison is the composite of three isomorphisms:

1. `SheafOfModules.symmetricPieceIso`, restricted to the slice site, which replaces the given
   symmetric algebra by `SheafOfModules.sectionwiseSymmetricAlgebra`;
2. `Stacks.SheafOfModules.SliceSheafification.sheafifyOverIso` — sheafification of presheaves of
   modules commutes with restriction to a slice site;
3. `PresheafOfModules.symPowOverIso` — the *presheaf* of sectionwise symmetric powers commutes
   with restriction on the nose, because it is defined sectionwise.

The exterior case is identical with `SheafOfModules.exteriorPieceIso` and
`PresheafOfModules.extPowOverIso`. Step 3 is the only new content and it is the identity on
sections; steps 1 and 2 are already in the library.

## Main definitions

* `PresheafOfModules.sliceRestrict`: restriction of presheaves of modules along
  `Over.forget U`, with no change of scalars. This is `PresheafOfModules.pushforward₀`, which is
  definitionally the `PresheafOfModules.pushforward` at the identity used by
  `Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor`.
* `PresheafOfModules.symPowOverAb` and `extPowOverAb` (with their inverses `symPowOverAbInv`,
  `extPowOverAbInv`): the comparison at the level of the underlying presheaves of abelian
  groups, which is the identity on sections.
* `PresheafOfModules.symPowOverIso` and `extPowOverIso`: **the presheaves of sectionwise
  symmetric and exterior powers commute with restriction to a slice site.**

## Main results

* `Stacks.SheafOfModules.sectionwiseSymmetricPowerOverIso` and
  `sectionwiseExteriorPowerOverIso`: the comparison for the sheafified sectionwise algebras of
  `SheafOfModules.sectionwiseSymmetricAlgebra` and `sectionwiseExteriorAlgebra`.
* `Stacks.SheafOfModules.symmetricPowerOverIso` and `exteriorPowerOverIso`: **the comparison for
  an arbitrary pair of algebras** — one symmetric (respectively exterior) algebra `A` of `M` on
  `(C, J)` and one, `B`, of `M|_U` on `(Over U, J.over U)`. These are the declarations a
  consumer uses; see the implementation notes for the interface.

## Implementation notes

**The interface.** The two headline isomorphisms are

```
Stacks.SheafOfModules.symmetricPowerOverIso (M) (U) (n) (A) (gen) (hA) (B) (gen') (hB) :
    (A.piece (n : ℤ)).over U ≅ B.piece (n : ℤ)
```

and its exterior counterpart, where `hA : IsSymmetricAlgebra A gen` and
`hB : IsSymmetricAlgebra B gen'`. At `A := A.symmetric` for a package
`A : SheafOfModules.TensorExteriorSymmetricAlgebras J M` of Section 17.21 the source is
`(A.symmetricPower n).over U` on the nose, since `symmetricPower n` is an abbreviation for
`symmetric.piece (n : ℤ)`. The target may always be taken to be the slice site's own sectionwise
symmetric algebra, whose universal property is
`SheafOfModules.isSymmetricAlgebra_sectionwiseSymmetricAlgebra_val`, so no symmetric algebra of
`M|_U` has to be produced in advance.

**Both algebras are hypotheses, and the sheaf of commutative rings over the slice is
`O♯.over U`.** Section 17.21 pins the symmetric algebra only up to canonical isomorphism, so a
statement about "the" symmetric power has to quantify over the choices; that is what makes `A`,
`B` and their universal properties arguments. `B` is declared over
`CategoryTheory.Sheaf.toRingCat (J.over U) (O♯.over U)`, which is *definitionally* the ring
sheaf `(toRingCat J O♯).over U` that `M.over U` lives over, but is the spelling in which the
implicit arguments of `SheafOfModules.symmetricPieceIso` are determined without higher-order
unification. The crossing happens once, at the application site.

**Why the comparison is built from `PresheafOfModules.homMk` rather than
`PresheafOfModules.isoMk`.** The two presheaves of modules being compared have *equal*
underlying presheaves of abelian groups, and `isoMk` would be the natural constructor; but it
asks for isomorphisms of the `ModuleCat` objects, and those carry the `Module` instance, which
is reached at the two spellings through `SymPow.symmetricPower` and `exteriorPower` — both
submodules of a quotient algebra. For the exterior power the resulting `isDefEq` query exhausts
the heartbeat budget even though the two instances are definitionally equal. `homMk` asks
instead for a morphism of the underlying presheaves of abelian groups, where `forget₂` has
already discarded the `Module` instance, so each object comparison is cheap; the linearity
obligation is then an equation between *elements*, which is `rfl`. The same construction is used
for the symmetric power, where `isoMk` does in fact go through, so that the two halves of the
file read the same way. Naturality is proved elementwise (`by ext x; rfl`) for the same reason:
the bundled identity of restriction maps is the query that blows up.

**No new `set_option`, and no raised heartbeat limit.** Every defeq above is discharged at the
default budget; the discipline that makes that possible is the one recorded in the previous note
plus naming the implicit arguments of `SheafOfModules.symmetricPieceIso` and
`exteriorPieceIso` at their slice instantiation.

**No `@[stacks]` attribute.** Tag 01CI is the statement that pullback commutes with the three
algebras along a *morphism of ringed spaces*, and its covering set is the two `@[stacks 01CI]`
declarations of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso` together with
`Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso` and its uniqueness statement in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullbackIso`; restriction to a
slice site of a general site is not a case of that, and nothing in Tag 01CL or 01CK asserts
this statement either. It is infrastructure for the Tag 01CL assembly — the hypothesis `p` of
`SheafOfModules.TensorExteriorSymmetricAlgebras.isQuasicoherent_symmetricAlgebraSheaf` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentGradedCoprod` — rather than a tagged
assertion of its own.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Sheaf Opposite
  Stacks.SheafOfModules.SliceSheafification

namespace PresheafOfModules

section SlicePresheaf

variable {C : Type u} [Category.{v} C] (U : C) {O : Cᵒᵖ ⥤ CommRingCat.{w}} (n : ℕ)
  (P : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-- Restriction of presheaves of modules to the slice site over `U`, with no change of
scalars. -/
noncomputable abbrev sliceRestrict :
    PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⥤
      PresheafOfModules.{w} ((Over.forget U).op ⋙ (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :=
  pushforward₀.{w} (Over.forget U) (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})

/-! ### Symmetric powers -/

/-- The identity map of underlying presheaves of abelian groups, from the restriction of the
presheaf of sectionwise symmetric powers to the presheaf of sectionwise symmetric powers of the
restriction. -/
noncomputable def symPowOverAb :
    ((sliceRestrict U (O := O)).obj (symPow n P)).presheaf ⟶
      (symPow (O := (Over.forget U).op ⋙ O) n ((sliceRestrict U (O := O)).obj P)).presheaf where
  app X := 𝟙 (((sliceRestrict U (O := O)).obj (symPow n P)).presheaf.obj X)
  naturality _ _ _ := by ext x; rfl

/-- The inverse of `PresheafOfModules.symPowOverAb`, again the identity on sections. -/
noncomputable def symPowOverAbInv :
    (symPow (O := (Over.forget U).op ⋙ O) n ((sliceRestrict U (O := O)).obj P)).presheaf ⟶
      ((sliceRestrict U (O := O)).obj (symPow n P)).presheaf where
  app X := 𝟙 ((symPow (O := (Over.forget U).op ⋙ O) n
    ((sliceRestrict U (O := O)).obj P)).presheaf.obj X)
  naturality _ _ _ := by ext x; rfl

/-- **The presheaf of sectionwise symmetric powers commutes with restriction to a slice site.**
The comparison is the identity on sections. -/
noncomputable def symPowOverIso :
    (sliceRestrict U (O := O)).obj (symPow n P) ≅
      symPow (O := (Over.forget U).op ⋙ O) n ((sliceRestrict U (O := O)).obj P) where
  hom := homMk (symPowOverAb U n P) (fun _ _ _ => rfl)
  inv := homMk (symPowOverAbInv U n P) (fun _ _ _ => rfl)
  hom_inv_id := by ext X x; rfl
  inv_hom_id := by ext X x; rfl

/-- The comparison of sectionwise symmetric powers is the identity on sections. -/
@[simp]
theorem symPowOverAb_app (X : (Over U)ᵒᵖ) : (symPowOverAb U n P).app X =
    𝟙 (((sliceRestrict U (O := O)).obj (symPow n P)).presheaf.obj X) := rfl

/-- `PresheafOfModules.symPowOverIso` is the comparison `PresheafOfModules.symPowOverAb` of
underlying presheaves of abelian groups, read as a morphism of presheaves of modules. -/
theorem symPowOverIso_hom :
    (symPowOverIso U n P).hom = homMk (symPowOverAb U n P) (fun _ _ _ => rfl) := rfl

/-! ### Exterior powers -/

/-- The identity map of underlying presheaves of abelian groups, from the restriction of the
presheaf of sectionwise exterior powers to the presheaf of sectionwise exterior powers of the
restriction. -/
noncomputable def extPowOverAb :
    ((sliceRestrict U (O := O)).obj (extPow n P)).presheaf ⟶
      (extPow (O := (Over.forget U).op ⋙ O) n ((sliceRestrict U (O := O)).obj P)).presheaf where
  app X := 𝟙 (((sliceRestrict U (O := O)).obj (extPow n P)).presheaf.obj X)
  naturality _ _ _ := by ext x; rfl

/-- The inverse of `PresheafOfModules.extPowOverAb`, again the identity on sections. -/
noncomputable def extPowOverAbInv :
    (extPow (O := (Over.forget U).op ⋙ O) n ((sliceRestrict U (O := O)).obj P)).presheaf ⟶
      ((sliceRestrict U (O := O)).obj (extPow n P)).presheaf where
  app X := 𝟙 ((extPow (O := (Over.forget U).op ⋙ O) n
    ((sliceRestrict U (O := O)).obj P)).presheaf.obj X)
  naturality _ _ _ := by ext x; rfl

/-- **The presheaf of sectionwise exterior powers commutes with restriction to a slice site.**
The comparison is the identity on sections. -/
noncomputable def extPowOverIso :
    (sliceRestrict U (O := O)).obj (extPow n P) ≅
      extPow (O := (Over.forget U).op ⋙ O) n ((sliceRestrict U (O := O)).obj P) where
  hom := homMk (extPowOverAb U n P) (fun _ _ _ => rfl)
  inv := homMk (extPowOverAbInv U n P) (fun _ _ _ => rfl)
  hom_inv_id := by ext X x; rfl
  inv_hom_id := by ext X x; rfl

/-- The comparison of sectionwise exterior powers is the identity on sections. -/
@[simp]
theorem extPowOverAb_app (X : (Over U)ᵒᵖ) : (extPowOverAb U n P).app X =
    𝟙 (((sliceRestrict U (O := O)).obj (extPow n P)).presheaf.obj X) := rfl

/-- `PresheafOfModules.extPowOverIso` is the comparison `PresheafOfModules.extPowOverAb` of
underlying presheaves of abelian groups, read as a morphism of presheaves of modules. -/
theorem extPowOverIso_hom :
    (extPowOverIso U n P).hom = homMk (extPowOverAb U n P) (fun _ _ _ => rfl) := rfl

end SlicePresheaf

end PresheafOfModules

namespace Stacks.SheafOfModules

open PresheafOfModules _root_.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (M : _root_.SheafOfModules.{w} (toRingCat J Osharp)) (U : C)
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  (n : ℕ)

/-- **The sheafified sectionwise symmetric power commutes with restriction to a slice site.** -/
noncomputable def sectionwiseSymmetricPowerOverIso :
    ((_root_.SheafOfModules.sectionwiseSymmetricAlgebra J (𝟙 Osharp.obj) M.val).piece
        (n : ℤ)).over U ≅
      (_root_.SheafOfModules.sectionwiseSymmetricAlgebra (J.over U) (𝟙 (Osharp.over U).obj)
        ((M.over U).val)).piece (n : ℤ) :=
  (sheafifyOverIso.{w} (toRingCat J Osharp) U (symPow n M.val)).symm ≪≫
    (sheafification.{w} (𝟙 ((toRingCat J Osharp).over U).obj)).mapIso (symPowOverIso U n M.val)

/-- **The sheafified sectionwise exterior power commutes with restriction to a slice site.** -/
noncomputable def sectionwiseExteriorPowerOverIso :
    ((_root_.SheafOfModules.sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).piece
        (n : ℤ)).over U ≅
      (_root_.SheafOfModules.sectionwiseExteriorAlgebra (J.over U) (𝟙 (Osharp.over U).obj)
        ((M.over U).val)).piece (n : ℤ) :=
  (sheafifyOverIso.{w} (toRingCat J Osharp) U (extPow n M.val)).symm ≪≫
    (sheafification.{w} (𝟙 ((toRingCat J Osharp).over U).obj)).mapIso (extPowOverIso U n M.val)

section Symmetric

variable (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat J Osharp))
  (gen : M ⟶ A.piece 1)
  (hA : _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A gen)
  (B : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat (J.over U) (Osharp.over U)))
  (gen' : M.over U ⟶ B.piece 1)
  (hB : _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra B gen')

/-- **Restriction to a slice site commutes with the symmetric power.** -/
noncomputable def symmetricPowerOverIso : (A.piece (n : ℤ)).over U ≅ B.piece (n : ℤ) :=
  (_root_.SheafOfModules.overFunctor (toRingCat J Osharp) U).mapIso
      (_root_.SheafOfModules.symmetricPieceIso M A gen hA (n : ℤ)).symm ≪≫
    sectionwiseSymmetricPowerOverIso M U n ≪≫
      _root_.SheafOfModules.symmetricPieceIso (J := J.over U) (Osharp := Osharp.over U)
        (M.over U) B gen' hB (n : ℤ)

end Symmetric

section Exterior

variable (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat J Osharp))
  (gen : M ⟶ A.piece 1)
  (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen)
  (B : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat (J.over U) (Osharp.over U)))
  (gen' : M.over U ⟶ B.piece 1)
  (hB : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra B gen')

/-- **Restriction to a slice site commutes with the exterior power.** -/
noncomputable def exteriorPowerOverIso : (A.piece (n : ℤ)).over U ≅ B.piece (n : ℤ) :=
  (_root_.SheafOfModules.overFunctor (toRingCat J Osharp) U).mapIso
      (_root_.SheafOfModules.exteriorPieceIso M A gen hA (n : ℤ)).symm ≪≫
    sectionwiseExteriorPowerOverIso M U n ≪≫
      _root_.SheafOfModules.exteriorPieceIso (J := J.over U) (Osharp := Osharp.over U)
        (M.over U) B gen' hB (n : ℤ)

end Exterior

end Stacks.SheafOfModules

end
