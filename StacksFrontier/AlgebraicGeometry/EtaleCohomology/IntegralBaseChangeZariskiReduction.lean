module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralBaseLeray

/-!
# The Zariski reduction of Stacks 0EYP

Stacks 0EYP asserts that for a cartesian square of schemes

```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```

with `f` integral and `F` a sheaf of sets on the small étale site of `X`, the base change map
`g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism.  This file reduces that statement to the case
where all four corners of the square are affine, by applying Stacks 0EZR part (1) to the Zariski
covering of `Y'` by the affine opens of the preimages of the affine opens of `Y`.

## Main results

* `Stacks.EtaleCohomology.zariskiIndex_cover` — the affine opens of the preimages `g⁻¹(W)` of the
  affine opens `W` of `Y` form an étale covering of `Y'`.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isIntegralHom_of_affine_case` —
  **Stacks 0EYP for an arbitrary cartesian square with integral bottom follows from Stacks 0EYP
  for cartesian squares all four of whose corners are affine.**
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace Stacks.EtaleCohomology

universe z v u

section Reduction

variable {X X' Y Y' : Scheme.{u}}

/-- **A jointly surjective family of open immersions is an étale covering.**  An open immersion
is étale, so this is the membership criterion for the étale precoverage together with joint
surjectivity. -/
lemma mem_etalePrecoverage_of_isOpenImmersion {Z : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}}
    (u : ∀ i, U i ⟶ Z) [∀ i, IsOpenImmersion (u i)]
    (h : ∀ x : Z, ∃ i, x ∈ Set.range (u i)) :
    Presieve.ofArrows U u ∈ Scheme.etalePrecoverage Z :=
  (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mpr ⟨h, fun _ ↦ inferInstance⟩

/-- The index set of the Zariski covering used to reduce Stacks 0EYP to the affine case: an
affine open `W` of `Y` together with an affine open `U` of `Y'` contained in `g⁻¹(W)`. -/
abbrev zariskiIndex (g : Y' ⟶ Y) : Type u :=
  Σ W : Y.affineOpens, {U : Y'.affineOpens // (U : Y'.Opens) ≤ g ⁻¹ᵁ (W : Y.Opens)}

/-- **The affine opens of the preimages of the affine opens of `Y` form an étale covering of
`Y'`.**  Every point of `Y'` lies in such a member: its image lies in some affine open `W` of
`Y`, and the affine opens contained in the open set `g⁻¹(W)` cover it. -/
lemma zariskiIndex_cover (g : Y' ⟶ Y) :
    Presieve.ofArrows (fun i : zariskiIndex g ↦ ((i.2.1 : Y'.Opens)).toScheme)
        (fun i ↦ ((i.2.1 : Y'.Opens)).ι) ∈ Scheme.etalePrecoverage Y' :=
  mem_etalePrecoverage_of_isOpenImmersion _ fun x ↦ by
    obtain ⟨W, hW, hxW, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y) (x := g.base x) (U := ⊤) trivial
    obtain ⟨U, hU, hxU, hsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y') (x := x) (U := g ⁻¹ᵁ W) hxW
    exact ⟨⟨⟨W, hW⟩, ⟨⟨U, hU⟩, hsub⟩⟩, by rw [Scheme.Opens.range_ι]; exact hxU⟩

/-- **The base change map is independent of which proof of the square's commutativity it is
written with.**  Two such proofs are equal, being proofs of the same proposition, so this is
substitution; it is stated because the kernel will not discharge the difference on its own.

Comparing two spellings of `Stacks.EtaleCohomology.smallEtaleSetsBaseChange` that differ in any
one argument — even in that proof, whose two sides have syntactically the same type — makes the
kernel unfold the base change map itself, hence the mate of the square comparison of composite
direct images, whose sections are what `Stacks.EtaleCohomology.OrdinaryLocal` is written never to
reduce; it does not finish within the default budget.  Substituting the proof away first leaves
nothing to compare. -/
private lemma isIso_smallEtaleSetsBaseChange_app_congr_w {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (w w' : g' ≫ f = f' ≫ g) (G : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (h : IsIso ((smallEtaleSetsBaseChange.{u, v} g' f' f g w).app G)) :
    IsIso ((smallEtaleSetsBaseChange.{u, v} g' f' f g w').app G) := by
  have hww : w = w' := rfl
  subst hww
  exact h

/-- **Stacks 0EZR part (1) with the whole outer square named.**  This is
`Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isIso_local` restated so that the
four corners of the outer square, its four morphisms, the proof that it commutes and the sheaf
are all arguments, identified with the corresponding fields of the data by hypotheses the caller
discharges by `rfl` and `HEq.rfl`.

Every one of those identifications has to be named, the four corners included.  The corners are
the implicit arguments of `Stacks.EtaleCohomology.smallEtaleSetsBaseChange`, so a form that
names only the morphisms still leaves the kernel comparing two spellings of the base change map
that differ in four arguments, which costs more than the default budget for the reason recorded
on `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_congr_w`.  With all of them
substituted away first, the two spellings inside are syntactically equal, and the conclusion
handed back to the caller is written in the caller's own corners, morphisms, proof and sheaf, so
nothing is compared there either. -/
private lemma isIso_smallEtaleSetsBaseChange_app_of_isIso_local'
    {X₀ Y₀ S₀ T₀ : Scheme.{u}} (e' : Y₀ ⟶ T₀) (h' : Y₀ ⟶ X₀) (g' : T₀ ⟶ S₀) (f' : X₀ ⟶ S₀)
    (F' : Sheaf T₀.smallEtaleTopology (Type (max (u + 1) v)))
    (w : e' ≫ g' = h' ≫ f')
    (D : EtaleLocalBaseChangeData.{u, z, _, _} (Type (max (u + 1) v)))
    (hX : X₀ = D.X) (hY : Y₀ = D.Y) (hS : S₀ = D.S) (hT : T₀ = D.T)
    (he : HEq e' D.e) (hh : HEq h' D.h) (hg : HEq g' D.g) (hf : HEq f' D.f)
    (hF : HEq F' D.F)
    (hlocal : ∀ i, IsIso ((smallEtaleSetsBaseChange.{u, v} (D.e_i i) (D.h_i i) (D.g_i i)
      (D.f_i i) (D.local_cartesian i).w.symm).app
        ((smallEtaleInverseImage.{u, v} (D.toT_i i)).obj D.F))) :
    IsIso ((smallEtaleSetsBaseChange.{u, v} e' h' g' f' w).app F') := by
  subst hX hY hS hT
  obtain rfl := eq_of_heq he
  obtain rfl := eq_of_heq hh
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hF
  exact isIso_smallEtaleSetsBaseChange_app_congr_w D.e D.h D.g D.f D.cartesian.w.symm w D.F
    (isIso_smallEtaleSetsBaseChange_app_of_isIso_local D hlocal)

/-- **The data of Stacks 0EZR attached to a cartesian square with integral bottom.**  For a
cartesian square

```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```

and a sheaf `F` of sets on the small étale site of `X`, this is the data of Stacks 0EZR for the
square read in the orientation

```
Y' <--f'-- X'
|g         |g'
Y  <--f--  X
```

with the étale covering of `Y'` taken to be the Zariski covering
`Stacks.EtaleCohomology.zariskiIndex_cover` by the affine opens `U` of the preimages `g⁻¹(W)` of
the affine opens `W` of `Y`, each member `U` factoring through the affine open `W` it was chosen
inside by the restriction of `g`.  The two fibre products at each index are the chosen pullbacks
`U ×_{Y'} X'` and `W ×_Y X`, and the diagonal of the local square and its cartesianness are
`Stacks.EtaleCohomology.localSquareDiag` and
`Stacks.EtaleCohomology.isPullback_localSquare`. -/
noncomputable def zariskiData (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))) :
    EtaleLocalBaseChangeData.{u, u, _, _} (Type (max (u + 1) v)) where
  X := Y'
  Y := X'
  S := Y
  T := X
  f := g
  h := f'
  e := g'
  g := f
  cartesian := sq.flip
  I := zariskiIndex g
  U i := ((i.2.1 : Y'.Opens)).toScheme
  u i := ((i.2.1 : Y'.Opens)).ι
  cover := zariskiIndex_cover g
  V i := ((i.1 : Y.Opens)).toScheme
  v i := ((i.1 : Y.Opens)).ι
  etale_v _ := inferInstance
  f_i i := g.resLE _ _ i.2.2
  factorization i := Scheme.Hom.resLE_comp_ι g i.2.2
  Y_i i := pullback ((i.2.1 : Y'.Opens)).ι f'
  h_i _ := pullback.fst _ _
  toY_i _ := pullback.snd _ _
  upper_cartesian _ := IsPullback.of_hasPullback _ _
  T_i i := pullback ((i.1 : Y.Opens)).ι f
  g_i _ := pullback.fst _ _
  toT_i _ := pullback.snd _ _
  lower_cartesian _ := IsPullback.of_hasPullback _ _
  e_i i := localSquareDiag sq.flip (Scheme.Hom.resLE_comp_ι g i.2.2)
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
  e_i_compatible _ := localSquareDiag_comp_snd _ _ _ _
  local_cartesian _ := isPullback_localSquare _ _ _ _
  F := F

section Local

variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (sq : IsPullback g' f' f g) (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))

/-! The four corners of the `i`-th local square of `Stacks.EtaleCohomology.zariskiData` are
affine and its left vertical morphism is integral.  Each is registered in the spelling the local
square's own statement uses, namely as a field of the data, so that the appeal to the all-affine
case needs no comparison of two spellings of the same scheme. -/

/-- The left vertical morphism `W ×_Y X ⟶ W` of the `i`-th local square is integral, being a
base change of the integral `f`. -/
private instance isIntegralHom_zariskiData_g_i [IsIntegralHom f] (i) :
    IsIntegralHom ((zariskiData g' f' f g sq F).g_i i) :=
  inferInstanceAs (IsIntegralHom (pullback.fst ((i.1 : Y.Opens)).ι f))

/-- The lower left corner `W` of the `i`-th local square is affine, by choice of the covering. -/
private instance isAffine_zariskiData_V (i) : IsAffine ((zariskiData g' f' f g sq F).V i) :=
  inferInstanceAs (IsAffine ((i.1 : Y.Opens)).toScheme)

/-- The upper left corner `U` of the `i`-th local square is affine, by choice of the
covering. -/
private instance isAffine_zariskiData_U (i) : IsAffine ((zariskiData g' f' f g sq F).U i) :=
  inferInstanceAs (IsAffine ((i.2.1 : Y'.Opens)).toScheme)

/-- The lower right corner `W ×_Y X` of the `i`-th local square is affine: `f` is integral hence
affine, and `W` is affine. -/
private instance isAffine_zariskiData_T_i [IsIntegralHom f] (i) :
    IsAffine ((zariskiData g' f' f g sq F).T_i i) :=
  inferInstanceAs (IsAffine (pullback ((i.1 : Y.Opens)).ι f))

/-- The upper right corner `U ×_{Y'} X'` of the `i`-th local square is affine: `f'` is integral,
being a base change of `f`, hence affine, and `U` is affine. -/
private instance isAffine_zariskiData_Y_i [IsIntegralHom f'] (i) :
    IsAffine ((zariskiData g' f' f g sq F).Y_i i) :=
  inferInstanceAs (IsAffine (pullback ((i.2.1 : Y'.Opens)).ι f'))

end Local


/-- **Stacks 0EYP for an arbitrary cartesian square with integral bottom follows from Stacks
0EYP for cartesian squares all four of whose corners are affine.**  Let

```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```

be a cartesian square with `f` integral and let `F` be a sheaf of sets on the small étale site of
`X`.  If the base change map `b⁻¹ a_* G ⟶ a'_* (b')⁻¹ G` is invertible for every cartesian square

```
Z' --b'--> Z
|a'        |a
A' --b-->  A
```

with `a` integral and `A`, `A'`, `Z`, `Z'` all affine, and every sheaf `G` of sets on the small
étale site of `Z`, then the base change map `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` of the given square is
invertible.

The covering of `Y'` to which Stacks 0EZR part (1) is applied, through
`Stacks.EtaleCohomology.zariskiData`, is the Zariski covering by the affine opens `U` of the
preimages `g⁻¹(W)` of the affine opens `W` of `Y`.  The four corners of the resulting local
square are affine: `W` and `U` by choice, `W ×_Y X` because `f` is integral hence affine and `W`
is affine, and `U ×_{Y'} X'` because `f'` is integral, being a base change of `f`, and `U` is
affine.  Its left vertical morphism `W ×_Y X ⟶ W` is integral, again as a base change of `f`, so
the hypothesis applies to it. -/
theorem isIso_smallEtaleSetsBaseChange_app_of_isIntegralHom_of_affine_case
    (haff : ∀ (A A' Z Z' : Scheme.{u}) (a : Z ⟶ A) (b : A' ⟶ A) (b' : Z' ⟶ Z) (a' : Z' ⟶ A')
      (sq : IsPullback b' a' a b), IsIntegralHom a → IsAffine A → IsAffine A' → IsAffine Z →
      IsAffine Z' → ∀ G : Sheaf Z.smallEtaleTopology (Type (max (u + 1) v)),
        IsIso ((smallEtaleSetsBaseChange.{u, v} b' a' a b sq.w).app G))
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))) :
    IsIso ((smallEtaleSetsBaseChange.{u, v} g' f' f g sq.w).app F) := by
  have : IsIntegralHom f' := isIntegralHom_of_isPullback sq.flip
  refine isIso_smallEtaleSetsBaseChange_app_of_isIso_local' g' f' f g F sq.w
    (zariskiData g' f' f g sq F) rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    fun i ↦ ?_
  refine isIso_smallEtaleSetsBaseChange_app_congr_w _ _ _ _
    (((zariskiData g' f' f g sq F).local_cartesian i).flip).w _ _ ?_
  exact haff _ _ _ _ _ _ _ _ ((zariskiData g' f' f g sq F).local_cartesian i).flip
    (isIntegralHom_zariskiData_g_i g' f' f g sq F i)
    (isAffine_zariskiData_V g' f' f g sq F i)
    (isAffine_zariskiData_U g' f' f g sq F i)
    (isAffine_zariskiData_T_i g' f' f g sq F i)
    (isAffine_zariskiData_Y_i g' f' f g sq F i) _

end Reduction

end Stacks.EtaleCohomology
