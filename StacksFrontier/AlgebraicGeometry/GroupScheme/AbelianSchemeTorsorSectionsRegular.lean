module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyInjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.RegularRationalSectionExtension

/-!
# Sections of torsors under an abelian scheme over a regular base

Let `W` be a regular integral Noetherian scheme with function field `K` and let `G → W` be an
abelian scheme. For every fppf `G`-torsor `P` the restriction map `P(W) → P(K)` on sections is
bijective, and the restriction map `H¹_fppf(W, G) → H¹_fppf(Spec K, G)` is injective
([Stacks, Tag 0H8E]). No bound on the dimension of `W` enters.

## Main results

* `AlgebraicGeometry.isTrivial_of_nonempty_sections_genericPoint_of_isRegular`: an fppf
  `G`-torsor with a section over `Spec K` is trivial.
* `AlgebraicGeometry.surjective_torsorSectionsRestrictGenericPoint_trivialTorsor`: the
  restriction map `G(W) → G(K)` on the points of `G` is surjective.
* `AlgebraicGeometry.bijective_torsorSectionsRestrictGenericPoint`: **Stacks 0H8E**, part (1).
* `AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_isRegular`: **Stacks 0H8E**,
  part (2).

## Implementation notes

The geometric input is `AlgebraicGeometry.GroupScheme.exists_section_extending_of_regular`: a
section over the generic point of a proper group scheme over an integral Noetherian regular
scheme extends to a section. The source obtains the extension of rational sections from the
identification of `G` with the identity component of the Picard scheme of the dual abelian scheme;
the extension theorem used here is proved instead by induction on the dimension of the local
rings, from the case of dimension at most two (the resolution argument of Tag 0AF9) and, in
dimension at least three, Krull's height theorem together with algebraic Hartogs. It holds for
every proper group scheme, so it applies to the abelian scheme `G` and to its base changes along
étale morphisms.

A torsor with a section over `Spec K` is trivial by the gluing argument of
`AlgebraicGeometry.isTrivial_of_nonempty_genericPoint_of_extend_of_local`: étale locally it has a
section, the generic section differs from it by a rational section of `G`, which extends, and the
local extensions glue. For a trivial torsor the restriction map is the map `G(W) → G(K)`, which is
injective (`AlgebraicGeometry.injective_torsorSectionsRestrictGenericPoint`) and surjective by the
extension theorem; so the restriction map of every torsor is bijective, which is part (1). Part (2)
follows from part (1) as in the source
(`AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_surjective_sections`).

## References

* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
* [Stacks Project, Tag 0H8E](https://stacks.math.columbia.edu/tag/0H8E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)

/-- **An fppf torsor under an abelian scheme over a regular integral Noetherian scheme with a
section over the generic point is trivial.** No bound on the dimension of the base enters: the
rational sections of the abelian scheme over the integral étale neighbourhoods of the base extend
by `AlgebraicGeometry.GroupScheme.exists_section_extending_of_regular`. -/
public theorem isTrivial_of_nonempty_sections_genericPoint_of_isRegular
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (hreg : IsRegular W)
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG))
    (hne : Nonempty (F.1.presheaf.obj (op (genericPointObj B W hW hK)))) :
    F.1.IsTrivial :=
  isTrivial_of_nonempty_genericPoint_of_extend_of_local B W hW hreg (n := ⊤) le_top hK G hG
    (fun X _ _ hX _ H _ _ σ hσ => GroupScheme.exists_section_extending_of_regular X hX H σ hσ)
    (fun G' _ _ _ hG' F' w => exists_etale_section_of_torsor B W hW G' hG' F' w) F hne

/-- **The restriction map `G(W) → G(K)` on the points of a proper group scheme over a regular
integral Noetherian scheme is surjective**: a point of `G` over the generic point is the
restriction of a section of `G ⟶ W`, by
`AlgebraicGeometry.GroupScheme.exists_section_extending_of_regular`. The sections of the trivial
torsor under the sheaf of points of `G` are the points of `G`, so this is the restriction map of
the trivial torsor. -/
public theorem surjective_torsorSectionsRestrictGenericPoint_trivialTorsor
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (hreg : IsRegular W)
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsCommMonObj G] [IsProper G.hom] (hG : B.Contains G.left) :
    Function.Surjective (torsorSectionsRestrictGenericPoint B W hW hK G hG
      ⟨trivialTorsor _, trivialTorsor_isTorsor _⟩) := by
  intro a
  let a' : (Over.post (X := B.obj hW) B.inclusion).obj (genericPointObj B W hW hK) ⟶ G := a
  have hι : genericPointToBase B W hW hK =
      Over.homMk (genericPointObj B W hW hK).hom := Over.mkIdTerminal.hom_ext _ _
  have hιleft : ((Over.post (X := B.obj hW) B.inclusion).map
        (genericPointToBase B W hW hK)).left =
      W.fromSpecStalk (genericPoint (W : Type u)) := by
    change B.inclusion.map (genericPointToBase B W hW hK).left = _
    rw [hι]
    rfl
  have ha' : a'.left ≫ G.hom = W.fromSpecStalk (genericPoint W) := Over.w a'
  obtain ⟨g, hg1, hg2⟩ := GroupScheme.exists_section_extending_of_regular W hreg G a'.left ha'
  let b : (Over.post (X := B.obj hW) B.inclusion).obj (Over.mk (𝟙 (B.obj hW))) ⟶ G :=
    Over.homMk g hg1
  refine ⟨b, ?_⟩
  change (Over.post (X := B.obj hW) B.inclusion).map (genericPointToBase B W hW hK) ≫ b = a'
  apply Over.OverMorphism.ext
  rw [Over.comp_left, hιleft]
  exact hg2

/-- **Stacks 0H8E, part (1).** Let `W` be a regular integral Noetherian scheme with function
field `K` and let `G → W` be an abelian scheme. For every fppf `G`-torsor `P` the restriction map
`P(W) → P(K)` on sections is bijective. No bound on the dimension of `W` enters.

Injectivity is `AlgebraicGeometry.injective_torsorSectionsRestrictGenericPoint`. For
surjectivity, a torsor with a section over `Spec K` is trivial
(`AlgebraicGeometry.isTrivial_of_nonempty_sections_genericPoint_of_isRegular`), and by naturality
of the trivialising isomorphism its restriction map is conjugate to the map `G(W) → G(K)`, which is
surjective (`AlgebraicGeometry.surjective_torsorSectionsRestrictGenericPoint_trivialTorsor`).

The hypotheses `hW`, `hK` and `hG` only say that `W`, `Spec K` and `G` lie in the big fppf site
`B`; they fix the size of the site and assume nothing about torsors or sections. -/
@[stacks 0H8E "part (1): P(W) → P(K) is bijective for every fppf G-torsor P, with W noetherian, \
regular and integral and G → W an abelian scheme, exactly as in the source; no bound on the \
dimension of W. The surjectivity, that a rational section of P → W extends to a section, is \
proved from the extension of rational sections of proper group schemes over regular bases, \
GroupScheme.exists_section_extending_of_regular, which is established by induction on the \
dimension of the local rings (the surface case of Stacks 0AF9, then Krull's height theorem and \
algebraic Hartogs) in place of the Picard-scheme argument the source sketches; part (2) is \
fppfH1_restriction_genericPoint_injective_of_isRegular"]
public theorem bijective_torsorSectionsRestrictGenericPoint
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (hreg : IsRegular W)
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG)) :
    Function.Bijective (torsorSectionsRestrictGenericPoint B W hW hK G hG F) := by
  refine ⟨injective_torsorSectionsRestrictGenericPoint B W hW hreg hK G hG F, fun y => ?_⟩
  obtain ⟨φ, hφ⟩ :=
    isTrivial_of_nonempty_sections_genericPoint_of_isRegular B W hW hreg hK G hG F ⟨y⟩
  have hiso : IsIso φ.hom := hφ
  have hbij : ∀ X, Function.Bijective (φ.hom.app X) :=
    fun X => (isIso_iff_bijective _).mp inferInstance
  have hnat : ∀ z, torsorSectionsRestrictGenericPoint B W hW hK G hG F
        (φ.hom.app (op (Over.mk (𝟙 (B.obj hW)))) z) =
      φ.hom.app (op (genericPointObj B W hW hK))
        (torsorSectionsRestrictGenericPoint B W hW hK G hG
          ⟨trivialTorsor _, trivialTorsor_isTorsor _⟩ z) :=
    fun z => (NatTrans.naturality_apply φ.hom (genericPointToBase B W hW hK).op z).symm
  obtain ⟨a, rfl⟩ := (hbij _).surjective y
  obtain ⟨b, hb⟩ :=
    surjective_torsorSectionsRestrictGenericPoint_trivialTorsor B W hW hreg hK G hG a
  exact ⟨φ.hom.app _ b, by rw [hnat b, hb]⟩

/-- **Stacks 0H8E, part (2).** Let `W` be a regular integral Noetherian scheme with function
field `K` and let `G → W` be an abelian scheme. Then the restriction map
`H¹_fppf(W, G) → H¹_fppf(Spec K, G)` on first cohomology is injective. No bound on the dimension
of `W` enters.

As in the source, part (2) follows from part (1),
`AlgebraicGeometry.bijective_torsorSectionsRestrictGenericPoint`: a class in the kernel is the
class of a torsor with a section over `Spec K`, which by surjectivity on sections has a section
over `W`, so is trivial. The hypotheses `hW`, `hK` and `hG` only place `W`, `Spec K` and `G` in
the big fppf site `B`, and the instances on sheafification and `Ext` make the first cohomology
`H¹_fppf` defined. -/
@[stacks 0H8E "part (2): H¹_fppf(W, G) → H¹_fppf(Spec K, G) is injective, with W noetherian, \
regular and integral and G → W an abelian scheme, exactly as in the source; this is the \
conclusion of Stacks 0AF9 with its two-dimensionality assumption removed. It is derived from \
part (1), bijective_torsorSectionsRestrictGenericPoint, as in the source. The source's further \
remarks, that regularity may be weakened to local factoriality of smooth W-schemes and the \
attribution of the argument, carry no assertion"]
public theorem fppfH1_restriction_genericPoint_injective_of_isRegular
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (hreg : IsRegular W)
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    [HasSheafify (BigFppfOver.topology B W hW) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B W hW) AddCommGrpCat.{u})] :
    Function.Injective (((pointsSheaf B W hW G hG).cohomologyPresheaf 1).map
      (genericPointToBase B W hW hK).op) :=
  fppfH1_restriction_genericPoint_injective_of_surjective_sections B W hW hreg hK G hG
    fun F => (bijective_torsorSectionsRestrictGenericPoint B W hW hreg hK G hG F).2

end AlgebraicGeometry

end
