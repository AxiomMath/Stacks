module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Regular
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Stalk
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# Acyclicity of the Koszul complex of a sheaf is a stalkwise condition

Let `X` be a ringed space and `f₁, …, f_r ∈ Γ(X, O_X)`.  The Koszul complex
`K_•(O_X, f₁, …, f_r)` of Stacks tag 062L is a complex of sheaves of modules, and
`Stacks.AlgebraicGeometry.SeqKoszul.stalkIso` identifies its complex of stalks at a point `x`
with the ring-level Koszul complex `K_•(O_{X,x}, f₁,ₓ, …, f_r,ₓ)`.  Since a complex of sheaves of
modules is exact exactly when all its complexes of stalks are, the homology of `K_•(O_X, f_•)`
vanishes in a degree precisely when the homology of every ring-level Koszul complex of germs does.

That is the bridge which turns the two conditions of Stacks tag 063C — Koszul-regularity and
`H₁`-regularity of a family of sections — into the ring-theoretic conditions
`Koszul.IsKoszulRegular` and `Koszul.IsH1Regular` on the germs, where the whole ring-level theory
of Stacks tags 062E–062I is available.

## Main results

* `Stacks.AlgebraicGeometry.SeqKoszul.mapStalkComplexIso`: the complex of stalks of
  `K_•(O_X, f_•)` computed in abelian groups is the complex of stalks computed over the stalk
  ring.
* `Stacks.AlgebraicGeometry.SeqKoszul.isZero_homology_sheafComplex_iff`: the homology of
  `K_•(O_X, f_•)` vanishes in degree `n` exactly when the homology of `K_•(O_{X,x}, f_•,ₓ)` does
  for every `x`.
* `Stacks.AlgebraicGeometry.SeqKoszul.isKoszulRegularSequence_iff_forall_germ` and
  `Stacks.AlgebraicGeometry.SeqKoszul.isH1RegularSequence_iff_forall_germ`: a family of sections
  is a Koszul-regular (resp. `H₁`-regular) sequence exactly when each of its germ sequences is.

## Implementation notes

**The comparison is made in `AddCommGrpCat`, not over the stalk ring.**  The stalk of a sheaf of
`O_X`-modules carries two a priori different rings of scalars:
`AlgebraicGeometry.SheafOfModules.stalkObj` uses the stalk of `O_X` computed in `RingCat`, while
`Stacks.AlgebraicGeometry.SeqKoszul.stalkComplex` uses the stalk computed in `CommRingCat`.  Those
are isomorphic rings but not the same ring, so the two complexes of stalks do not even live in the
same category.  Exactness, however, is a condition on the underlying abelian groups, and those
*are* the same: the degree-`n` term of either is the stalk of the presheaf of abelian groups
underlying `U ↦ ⋀ⁿ(O_X(U)^r)`.  So the comparison is made after applying the faithful exact
functor `forget₂ (ModuleCat _) AddCommGrpCat`, and
`CategoryTheory.ShortComplex.exact_map_iff_of_faithful` moves exactness back across it.

The two short complexes on which `CategoryTheory.ShortComplex.Exact` is tested are reached without
transport: `((F.mapHomologicalComplex c).obj K).sc n = (K.sc n).map F` holds by `rfl`, so the
`n`-th short complex of a complex of stalks is literally the image under `F` of the `n`-th short
complex of the original, and likewise
`AlgebraicGeometry.SheafOfModules.stalkFunctor_comp_forget₂` is `rfl`.

The degree-`n` terms of the two complexes of abelian groups are definitionally equal, but the
elaborator will not see that while unifying the type of a morphism, because the filtered colimit
computing a stalk is opaque at that transparency.  The comparison isomorphism is therefore built
with `CategoryTheory.eqToIso`, whose components only ever need the *equality* of the two objects,
which `rfl` does prove; and its commuting squares are closed only after both differentials have
been rewritten to the underlying maps by `Stacks.AlgebraicGeometry.SeqKoszul.sheafComplex_d` and
`Stacks.RegularSequence.stalkComplex_d`, since before that each is a `dite` on `j + 1 = j + 1`
which does not reduce for a variable `j`.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.RegularSequence

universe u

namespace Stacks.AlgebraicGeometry.SeqKoszul

section General

/-- Exactness of a complex in one degree is invariant under isomorphism of complexes. -/
private theorem exactAt_iff_of_iso {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (e : K ≅ L) (n : ι) :
    K.ExactAt n ↔ L.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨fun h => h.of_iso ((HomologicalComplex.homologyFunctor C c n).mapIso e).symm,
    fun h => h.of_iso ((HomologicalComplex.homologyFunctor C c n).mapIso e)⟩

end General

variable (X : RingedSpace.{u, u}) (r : ℕ)
  (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))

/-- The functor taking a sheaf of `O_X`-modules to the stalk at `x` of its underlying presheaf of
abelian groups.  Exactness of a complex of sheaves of modules is tested through it. -/
abbrev stalkAb (x : X) : SheafOfModules.{u} (ringSheaf X) ⥤ AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor (ringSheaf X) x

/-- The stalk functor on sheaves of modules, valued in abelian groups, is additive, so it may be
applied to a complex degreewise.  Synthesis does not find this, because
`AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor` is a `def` and its additive factors
are invisible until it is unfolded; it is obtained instead from the additivity of the stalk
functor over the stalk ring. -/
instance stalkAb_additive (x : X) :
    (AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor (ringSheaf X) x).Additive := by
  rw [← AlgebraicGeometry.SheafOfModules.stalkFunctor_comp_forget₂]
  infer_instance

/-- **The two complexes of stalks of `K_•(O_X, f_•)` agree.**  Taking the stalk at `x` degreewise
in abelian groups gives the same complex as taking
`Stacks.AlgebraicGeometry.SeqKoszul.stalkComplex`, the complex of stalks over the stalk ring, and
forgetting its module structure: in degree `n` both are the stalk of the presheaf of abelian
groups underlying `U ↦ ⋀ⁿ(O_X(U)^r)`, with the map induced on stalks by the Koszul
differential. -/
def mapStalkComplexIso (x : X) :
    ((stalkAb X x).mapHomologicalComplex (ComplexShape.down ℕ)).obj (sheafComplex X r f) ≅
      ((forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (stalkComplex X r f x) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => eqToIso rfl) (by
    intro i j hij
    obtain rfl : j + 1 = i := hij
    have hd : (stalkComplex X r f x).d (j + 1) j =
        ModuleCat.ofHom (Stacks.RegularSequence.stalkD X f (piece X r) (pieceEquiv X r)
          (gen X r) (pieceEquiv_wedgeSection X r) (diff X r f) (pieceEquiv_diff X r f) j x) :=
      Stacks.RegularSequence.stalkComplex_d X f (piece X r) (pieceEquiv X r) (gen X r)
        (pieceEquiv_wedgeSection X r) (diff X r f) (pieceEquiv_diff X r f) x j
    simp only [Functor.mapHomologicalComplex_obj_d, sheafComplex_d, hd]
    rfl)

/-- **Vanishing of the homology of `K_•(O_X, f_•)` is a stalkwise condition.**  The homology of
the Koszul complex of a family of sections of the structure sheaf vanishes in degree `n` if and
only if, at every point, the homology of the ring-level Koszul complex of the germs of the family
vanishes in degree `n`. -/
theorem isZero_homology_sheafComplex_iff (n : ℕ) :
    IsZero ((sheafComplex X r f).homology n) ↔
      ∀ x : X, IsZero ((Koszul.seqComplex (germSequence X f x)).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff,
    AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact]
  refine forall_congr' fun x => ?_
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  have e1 : (AlgebraicGeometry.SheafOfModules.stalkShortComplex (ringSheaf X)
        ((sheafComplex X r f).sc n) x).Exact ↔
      (((stalkAb X x).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (sheafComplex X r f)).ExactAt n := Iff.rfl
  have e2 : (((forget₂ (ModuleCat.{u} (X.presheaf.stalk x))
          AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (stalkComplex X r f x)).ExactAt n ↔
      (stalkComplex X r f x).ExactAt n :=
    ((stalkComplex X r f x).sc n).exact_map_iff_of_faithful
      (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u})
  rw [e1, exactAt_iff_of_iso (mapStalkComplexIso X r f x) n, e2]
  exact (exactAt_iff_of_iso (stalkIso X r f x) n).symm

/-- **Koszul-regularity of a family of sections is Koszul-regularity of all its germ
sequences.**  This is the sheaf-to-ring bridge for the Koszul-regular half of Stacks tag 063C. -/
theorem isKoszulRegularSequence_iff_forall_germ :
    IsKoszulRegularSequence X f ↔ ∀ x : X, Koszul.IsKoszulRegular (germSequence X f x) :=
  ⟨fun h x i hi => (isZero_homology_sheafComplex_iff X r f i).mp (h i hi) x,
    fun h i hi => (isZero_homology_sheafComplex_iff X r f i).mpr fun x => h x i hi⟩

/-- **`H₁`-regularity of a family of sections is `H₁`-regularity of all its germ sequences.**
This is the sheaf-to-ring bridge for the `H₁`-regular half of Stacks tag 063C. -/
theorem isH1RegularSequence_iff_forall_germ :
    IsH1RegularSequence X f ↔ ∀ x : X, Koszul.IsH1Regular (germSequence X f x) :=
  isZero_homology_sheafComplex_iff X r f 1

end Stacks.AlgebraicGeometry.SeqKoszul

end
