module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceSetCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestriction
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfRepresentable

/-!
# The lower shriek of an étale morphism, and the transfer of Stacks 0GF6 to spaces-étale sheaves

Part (4) of Stacks 0GF6 reads `𝓕 ≅ f_{small,!} *`, where `f : X → Y` is étale and
`f_{small,!}` is the left adjoint of `f_small⁻¹` that exists by Stacks 03LP. This file
constructs that functor on sheaves of sets and computes it on the terminal sheaf, and it moves
the set-theoretic condition of the statement from the small étale site of `Y` to its
spaces-étale site, where the rest of the proof takes place.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleLowerShriek`: `f_{small,!}` for an étale morphism `f`,
  the left adjoint of restriction along the postcomposition functor `j` of Stacks 03LP; and
  `AlgebraicGeometry.Space.smallEtaleLowerShriekAdjunction`, its adjunction with the inverse
  image `f_small⁻¹` of Stacks 03G2, part (3).

## Main results

* `AlgebraicGeometry.Space.smallEtaleLowerShriekIso`: `f_{small,!}` is the left adjoint of
  restriction along spaces-étale postcomposition, conjugated by the comparison equivalences of
  Stacks 03G1.
* `AlgebraicGeometry.Space.smallEtaleLowerShriek_terminal_iso`: if the spaces-étale sheaf
  corresponding to `𝓕` is the sheafified representable of an algebraic space `W` étale over `Y`,
  then `𝓕 ≅ f_{small,!} *` for the structure morphism `f` of `W`.
* `AlgebraicGeometry.Space.SheafGivesSpace.exists_epi_of_satisfiesSetTheoreticCondition`: the
  set-theoretic condition of Stacks 0GF6 yields a surjection onto the corresponding
  spaces-étale sheaf from the sheafified representable of a scheme chart.

## Implementation notes

The terminal sheaf on the spaces-étale site of `X` is the sheafified representable of the
terminal object `SpacesEtale.idObj`, so the computation of `f_{small,!} *` is Stacks 04D3
(`sheafPullbackSheafifyYonedaIso`) for spaces-étale postcomposition, which sends that terminal
object to `W` itself.

## References

* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section LowerShriek

variable {X Y : AlgebraicSpaces B S hS}

/-- **The functor `f_{small,!}` of Stacks 0GF6, part (4).** For an étale morphism `f : X ⟶ Y`
the postcomposition functor `j : X_étale ⥤ Y_étale` of Stacks 03LP is continuous, and
`f_{small,!}` is the left adjoint of restriction along it, which is `f_small⁻¹` by Stacks 03LQ
(see `AlgebraicGeometry.Space.smallEtaleLowerShriekAdjunction`). -/
noncomputable abbrev smallEtaleLowerShriek (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)) :=
  (smallEtalePostcomp B S hS f hf).sheafPullback (Type (u + 1))
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)

/-- `f_{small,!}` is left adjoint to the inverse image `f_small⁻¹` of the morphism of small étale
topoi of Stacks 03G2, part (3): it is left adjoint to restriction along `j`, which is
`f_small⁻¹` by Stacks 03LQ. -/
noncomputable def smallEtaleLowerShriekAdjunction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    smallEtaleLowerShriek B S hS f hf ⊣ (smallToposMorphism B S hS f).inverseImage :=
  ((smallEtalePostcomp B S hS f hf).sheafAdjunctionContinuous (Type (u + 1))
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)).ofNatIsoRight
    (smallToposMorphism_inverseImageIso B S hS f hf).symm

/-- `f_{small,!}` is the left adjoint of restriction along spaces-étale postcomposition,
conjugated by the comparison equivalences of Stacks 03G1: both are left adjoints of
restriction along small étale postcomposition, because restricting along a chart of `X` after
postcomposition is restricting along the postcomposed chart. -/
noncomputable def smallEtaleLowerShriekIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    smallEtaleLowerShriek B S hS f hf ≅
      (smallEtaleToposEquiv B S hS X).inverse ⋙
        (spacesEtalePostcomp B S hS f hf).sheafPullback (Type (u + 1))
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
        (smallEtaleToposEquiv B S hS Y).functor :=
  let ΦX := smallEtaleToposEquiv B S hS X
  let ΦY := smallEtaleToposEquiv B S hS Y
  let P := (spacesEtalePostcomp B S hS f hf).sheafPushforwardContinuous (Type (u + 1))
    (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
  let Q := (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous (Type (u + 1))
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
  let adjP := (spacesEtalePostcomp B S hS f hf).sheafAdjunctionContinuous (Type (u + 1))
    (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
  let e : ΦY.inverse ⋙ P ⋙ ΦX.functor ≅ Q :=
    Functor.isoWhiskerLeft ΦY.inverse
        (smallEtaleToposEquiv_comp_postcomp_restriction B S hS f hf) ≪≫
      (Functor.associator ΦY.inverse ΦY.functor Q).symm ≪≫
      Functor.isoWhiskerRight ΦY.counitIso Q ≪≫ Functor.leftUnitor Q
  Adjunction.leftAdjointUniq
    ((smallEtalePostcomp B S hS f hf).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1))
    (((ΦX.symm.toAdjunction.comp adjP).comp ΦY.toAdjunction).ofNatIsoRight e)

end LowerShriek

/-- The terminal sheaf on the spaces-étale site of `X` is the sheafified representable of the
terminal object `SpacesEtale.idObj` of the site. -/
noncomputable def spacesEtaleTerminalIsoSheafifyYonedaIdObj (X : AlgebraicSpaces B S hS) :
    ⊤_ (Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) ≅
      (presheafToSheaf (SpacesEtale.topology B S hS X) (Type (u + 1))).obj
        (yoneda.obj (SpacesEtale.idObj B S hS X)) :=
  terminalIsTerminal.uniqueUpToIso
    (IsTerminal.isTerminalObj (presheafToSheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) _
      (IsTerminal.isTerminalObj yoneda _ (SpacesEtale.isTerminal_idObj B S hS X)))

/-- Postcomposing the terminal object `SpacesEtale.idObj` of the spaces-étale site of the
underlying space of `W` with its structure morphism gives back `W`. -/
noncomputable def spacesEtalePostcompIdObjIso {Y : AlgebraicSpaces B S hS}
    (W : SpacesEtale B S hS Y) :
    (spacesEtalePostcomp B S hS W.obj.hom W.property).obj
        (SpacesEtale.idObj B S hS W.obj.left) ≅ W :=
  ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) (by rfl))

/-- **Part (4) of Stacks 0GF6, from part (3).** Let `𝓕` be a sheaf of sets on the small étale
site of `Y` whose corresponding spaces-étale sheaf (Stacks 03G1) is the sheafified
representable `h_W^#` of an algebraic space `W` étale over `Y`, with structure morphism
`f : W → Y`. Then `𝓕 ≅ f_{small,!} *`, where `*` is the terminal sheaf on the small étale site
of `W`.

Through the comparison equivalences `f_{small,!}` is the left adjoint of restriction along
spaces-étale postcomposition (`AlgebraicGeometry.Space.smallEtaleLowerShriekIso`), the terminal
sheaf is the sheafified representable of the terminal object of the site, and Stacks 04D3
computes the left adjoint on it: it is the sheafified representable of the postcomposed
terminal object, which is `W`. -/
theorem smallEtaleLowerShriek_terminal_iso {Y : AlgebraicSpaces B S hS}
    (W : SpacesEtale B S hS Y) (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)))
    (α : (smallEtaleToposEquiv B S hS Y).inverse.obj F ≅
      (presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))).obj (yoneda.obj W)) :
    Nonempty (F ≅ (smallEtaleLowerShriek B S hS W.obj.hom W.property).obj
      (⊤_ (Sheaf (SmallEtale.topology B S hS W.obj.left.1) (Type (u + 1))))) := by
  let X := W.obj.left
  let f := W.obj.hom
  let hf : IsEtale B S hS f.hom := W.property
  let ΦX := smallEtaleToposEquiv B S hS X
  let ΦY := smallEtaleToposEquiv B S hS Y
  let J := spacesEtalePostcomp B S hS f hf
  let KX := SpacesEtale.topology B S hS X
  let KY := SpacesEtale.topology B S hS Y
  let Jsh := J.sheafPullback (Type (u + 1)) KX KY
  let e₁ : ΦX.inverse.obj (⊤_ (Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))) ≅
      (presheafToSheaf KX (Type (u + 1))).obj (yoneda.obj (SpacesEtale.idObj B S hS X)) :=
    (terminalIsTerminal.isTerminalObj ΦX.inverse _).uniqueUpToIso terminalIsTerminal ≪≫
      spacesEtaleTerminalIsoSheafifyYonedaIdObj B S hS X
  let e₂ : Jsh.obj ((presheafToSheaf KX (Type (u + 1))).obj
        (yoneda.obj (SpacesEtale.idObj B S hS X))) ≅
      (presheafToSheaf KY (Type (u + 1))).obj (yoneda.obj W) :=
    sheafPullbackSheafifyYonedaIso J KX KY (SpacesEtale.idObj B S hS X) ≪≫
      (presheafToSheaf KY (Type (u + 1))).mapIso
        (yoneda.mapIso (spacesEtalePostcompIdObjIso B S hS W))
  exact ⟨(ΦY.counitIso.app F).symm ≪≫ ΦY.functor.mapIso (α ≪≫ e₂.symm ≪≫ Jsh.mapIso e₁.symm) ≪≫
    ((smallEtaleLowerShriekIso B S hS f hf).app _).symm⟩

namespace SheafGivesSpace

/-- **The set-theoretic condition of Stacks 0GF6 on the spaces-étale site.** If `𝓕` satisfies
the condition, some scheme chart `V` of `Y` has a sheafified representable on the
spaces-étale site surjecting onto the spaces-étale sheaf corresponding to `𝓕` under the
comparison equivalence of Stacks 03G1.

The surjection `h_V^# → 𝓕` on the small étale site is a section `s ∈ 𝓕(V)`; the corresponding
section of the spaces-étale sheaf over the comparison object of `V` defines the map, and its
restriction to the small étale site factors the given surjection, hence is surjective, and an
equivalence reflects epimorphisms. -/
theorem exists_epi_of_satisfiesSetTheoreticCondition {Y : AlgebraicSpaces B S hS}
    {F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))}
    (hF : SatisfiesSetTheoreticCondition B S hS Y F) :
    ∃ (V : SmallEtale B S hS Y.1)
      (e : (presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))).obj
          (yoneda.obj ((comparisonFunctor B S hS Y).obj V)) ⟶
        (smallEtaleToposEquiv B S hS Y).inverse.obj F), Epi e := by
  obtain ⟨V, e₀, he₀⟩ := (satisfiesSetTheoreticCondition_iff B S hS Y F).1 hF
  let Φ := smallEtaleToposEquiv B S hS Y
  let K := SpacesEtale.topology B S hS Y
  let cV := (comparisonFunctor B S hS Y).obj V
  let H := (presheafToSheaf K (Type (u + 1))).obj (yoneda.obj cV)
  let J := SmallEtale.topology B S hS Y.1
  let s₀ : F.obj.obj (op V) := Sheaf.sectionEquiv J e₀
  let t : (Φ.inverse.obj F).obj.obj (op cV) := (Φ.counitIso.inv.app F).hom.app (op V) s₀
  let e : H ⟶ Φ.inverse.obj F :=
    ((sheafificationAdjunction K (Type (u + 1))).homEquiv _ _).symm (yonedaEquiv.symm t)
  refine ⟨V, e, ?_⟩
  let τ : (Φ.functor.obj H).obj.obj (op V) := (toSheafify K (yoneda.obj cV)).app (op cV) (𝟙 cV)
  let m : (Sheaf.sheafifiedYoneda J).obj V ⟶ Φ.functor.obj H :=
    (Sheaf.sectionEquiv J).symm τ
  have het : e.hom.app (op cV) τ = t := by
    have h : (sheafificationAdjunction K (Type (u + 1))).homEquiv _ _ e = yonedaEquiv.symm t :=
      Equiv.apply_symm_apply _ _
    rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
    simpa [τ] using congrArg (fun k => k.app (op cV) (𝟙 cV)) h
  have hfac : m ≫ Φ.functor.map e ≫ Φ.counitIso.hom.app F = e₀ := by
    apply (Sheaf.sectionEquiv J).injective
    rw [Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply]
    show (Φ.counitIso.hom.app F).hom.app (op V) (e.hom.app (op cV) τ) = s₀
    rw [het]
    show ((Φ.counitIso.inv.app F ≫ Φ.counitIso.hom.app F).hom.app (op V)) s₀ = s₀
    rw [Iso.inv_hom_id_app]
    rfl
  have h₁ : Epi (Φ.functor.map e ≫ Φ.counitIso.hom.app F) := epi_of_epi_fac hfac
  have h₂ : Epi (Φ.functor.map e) := by
    have hre : Φ.functor.map e =
        (Φ.functor.map e ≫ Φ.counitIso.hom.app F) ≫ Φ.counitIso.inv.app F := by
      simp
    rw [hre]
    exact epi_comp _ _
  exact Φ.functor.epi_of_epi_map h₂

end SheafGivesSpace

end AlgebraicGeometry.Space

end
