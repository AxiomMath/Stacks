module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.LocalTriviality

/-!
# Sections of a torsor under an abelian scheme and the generic point

Let `W` be a regular integral Noetherian scheme with function field `K` and let `G → W` be an
abelian scheme. For every fppf `G`-torsor `P` the restriction map `P(W) → P(K)` on sections is
bijective, and consequently `H¹_fppf(W, G) → H¹_fppf(Spec K, G)` is injective. No bound on the
dimension of `W` is needed for either assertion.

## Main definitions

* `AlgebraicGeometry.torsorSectionsRestrictGenericPoint` is the restriction map `P(W) → P(K)`
  on the sections of an fppf torsor `P` under the sheaf of points of `G`, taken along the
  canonical morphism `Spec K → W` of the big fppf site over `W`.

## Main results

* `AlgebraicGeometry.isTrivial_of_nonempty_sections_genericPoint_of_surjective`: a torsor whose
  restriction map on sections is surjective and which has a section over `Spec K` is trivial.
* `AlgebraicGeometry.injective_torsorSectionsRestrictGenericPoint_trivialTorsor`: the
  restriction map `G(W) → G(K)` on the points of `G` is injective.
* `AlgebraicGeometry.injective_torsorSectionsRestrictGenericPoint`: **Stacks 0H8E**, the
  injectivity half of part (1), for every fppf `G`-torsor and with no hypothesis on the
  dimension of `W`.
* `AlgebraicGeometry.bijective_torsorSectionsRestrictGenericPoint_of_surjective`: part (1)
  itself, with its surjectivity half assumed.
* `AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_isTrivial`: **Stacks 0H8E**,
  part (2), again with no hypothesis on the dimension of `W`.
* `AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_surjective_sections`: part (2)
  along the route the source takes through part (1).

## Implementation notes

The sections of `P` over `W` are the sections over the terminal object `Over.mk (𝟙 W)` of the
big fppf site over `W`, and the sections over `Spec K` are the sections over
`AlgebraicGeometry.genericPointObj`; the map between them is the functoriality of the presheaf
underlying `P` along `AlgebraicGeometry.genericPointToBase`, so there is no separate restriction
datum. Torsors are `Stacks.Cohomology.Torsors.AbelianTorsor` of the abelian sheaf
`AlgebraicGeometry.pointsSheaf` of points of `G`, as for Tag 0AF9. The trivial torsor under that
sheaf has the points of `G` for its sections, so the restriction map of the trivial torsor is the
map `G(W) → G(K)` on the `W`-points of `G`.

**Injectivity.** A torsor with a section over `W` has a section over the terminal object of the
site, hence is trivial (Tag 03AI, here through `PseudoTorsor.isTrivial_of_terminal_section`); a
torsor with no section over `W` has an injective restriction map for want of two sections to
separate. So injectivity reduces, by naturality of the trivialising isomorphism, to injectivity
of `G(W) → G(K)`, which is the statement that two sections of `G → W` agreeing over the generic
point agree. The latter holds because `G → W` is separated, `W` is reduced and `Spec K → W` is
dominant: its image is the set of points specialising to the generic point, and the closure of
the generic point is all of `W`.

**Surjectivity**, which is the statement that the schematic closure of a rational section of
`P → W` is a section, is not proved here and is a hypothesis. The source obtains it from the
regularity of `W` by identifying `G` with the identity component of the Picard scheme of the
dual abelian scheme and extending a generically defined invertible sheaf over a regular base;
neither the dual abelian scheme nor that identity component is available here. For regularity of
`W` it is enough that smooth `W`-schemes be locally factorial.

**Part (2)** is proved from the triviality of the torsors with a section over `Spec K`, as in
Tag 0AF9 and with no hypothesis on the dimension of `W`: a class in the kernel of the
restriction map on first cohomology is the class of a torsor with a section over `Spec K`
(Tag 03AJ), hence of a trivial torsor, hence zero. Surjectivity on sections for every torsor
supplies that triviality, which is the route the source takes.

As in Tag 0AF9, regularity and Noetherianness of `W` are the hypotheses of the source statement
and are not used below; integrality of `W` is used, since the generic point and the function
field are taken from it, as is properness of `G → W`, which makes `G → W` separated.

## References

* [Stacks Project, Tag 03AI](https://stacks.math.columbia.edu/tag/03AI)
* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
* [Stacks Project, Tag 0H8E](https://stacks.math.columbia.edu/tag/0H8E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)

/-- The restriction map `P(W) → P(K)` on the sections of an fppf torsor `P` under the sheaf of
points of a commutative group scheme `G` over an irreducible `W`: the functoriality of the
presheaf underlying `P` along the canonical morphism `Spec K ⟶ W` of the big fppf site over
`W`, whose terminal object is `Over.mk (𝟙 W)`. -/
public def torsorSectionsRestrictGenericPoint [IrreducibleSpace W]
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsCommMonObj G] (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG)) :
    F.1.presheaf.obj (op (Over.mk (𝟙 (B.obj hW)))) →
      F.1.presheaf.obj (op (genericPointObj B W hW hK)) :=
  F.1.presheaf.map (genericPointToBase B W hW hK).op

/-- **A torsor with a section over the generic point onto which the sections over `W` surject is
trivial.** The surjection produces a section over `W`, which is a section over the terminal
object of the big fppf site over `W`, that is, a global section of the torsor; and a torsor with
a global section is trivial. -/
public theorem isTrivial_of_nonempty_sections_genericPoint_of_surjective [IrreducibleSpace W]
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsCommMonObj G] (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG))
    (hsurj : Function.Surjective (torsorSectionsRestrictGenericPoint B W hW hK G hG F))
    (hne : Nonempty (F.1.presheaf.obj (op (genericPointObj B W hW hK)))) :
    F.1.IsTrivial := by
  obtain ⟨x⟩ := hne
  obtain ⟨y, -⟩ := hsurj x
  exact PseudoTorsor.isTrivial_of_terminal_section Over.mkIdTerminal F.1 y

/-- **The restriction map `G(W) → G(K)` on the points of a proper group scheme over an integral
scheme is injective**: two sections of `G ⟶ W` whose composites with the canonical morphism
`Spec K ⟶ W` agree are equal, because `G ⟶ W` is separated, `W` is reduced and `Spec K ⟶ W` is
dominant. The sections of the trivial torsor under the sheaf of points of `G` are the points of
`G`, so this is the restriction map of the trivial torsor. -/
public theorem injective_torsorSectionsRestrictGenericPoint_trivialTorsor
    [IsIntegral W] (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsCommMonObj G] [IsProper G.hom] (hG : B.Contains G.left) :
    Function.Injective (torsorSectionsRestrictGenericPoint B W hW hK G hG
      ⟨trivialTorsor _, trivialTorsor_isTorsor _⟩) := by
  intro a b hab
  let a' : (Over.post (X := B.obj hW) B.inclusion).obj (Over.mk (𝟙 (B.obj hW))) ⟶ G := a
  let b' : (Over.post (X := B.obj hW) B.inclusion).obj (Over.mk (𝟙 (B.obj hW))) ⟶ G := b
  have key : (Over.post (X := B.obj hW) B.inclusion).map (genericPointToBase B W hW hK) ≫ a' =
      (Over.post (X := B.obj hW) B.inclusion).map (genericPointToBase B W hW hK) ≫ b' := hab
  have hι : genericPointToBase B W hW hK =
      Over.homMk (genericPointObj B W hW hK).hom := Over.mkIdTerminal.hom_ext _ _
  have hιleft : ((Over.post (X := B.obj hW) B.inclusion).map
        (genericPointToBase B W hW hK)).left =
      W.fromSpecStalk (genericPoint (W : Type u)) := by
    change B.inclusion.map (genericPointToBase B W hW hK).left = _
    rw [hι]
    rfl
  have hd : IsDominant ((Over.post (X := B.obj hW) B.inclusion).map
      (genericPointToBase B W hW hK)).left := by
    rw [hιleft]
    exact isDominant_fromSpecStalk_genericPoint W
  have hred : IsReduced (unop ((Over.post (X := B.obj hW) B.inclusion).op.obj
      (op (Over.mk (𝟙 (B.obj hW)))))).left := inferInstanceAs (IsReduced W)
  have hleft := congrArg Over.Hom.left key
  rw [Over.comp_left, Over.comp_left] at hleft
  exact Over.OverMorphism.ext (AlgebraicGeometry.ext_of_isDominant_of_isSeparated G.hom
    ((Over.w a').trans (Over.w b').symm) _ hleft)

/-- **Stacks 0H8E, the injectivity half of part (1).** Let `W` be a regular integral Noetherian
scheme with function field `K` and let `G → W` be an abelian scheme. For every fppf `G`-torsor
`P` the restriction map `P(W) → P(K)` on sections is injective. No hypothesis on the dimension of
`W` enters.

A torsor with no section over `W` has nothing to separate. A torsor with one is trivial, and by
naturality of the trivialising isomorphism its restriction map is then conjugate to the
restriction map `G(W) → G(K)` on the points of `G`, which is injective. -/
@[stacks 0H8E "part (1), the injectivity half, for every G-torsor and with the \
two-dimensionality hypothesis of Stacks 0AF9 absent: the hypotheses on W are exactly \
noetherian, regular and integral. The surjectivity half of part (1) is the statement that the \
schematic closure of a rational section of P → W is a section; it is not proved, and is the \
hypothesis hsurj of bijective_torsorSectionsRestrictGenericPoint_of_surjective, which states \
part (1) in full. The tag obtains surjectivity by identifying G with the identity component of \
the Picard scheme of the dual abelian scheme and extending a generically defined invertible \
sheaf over the regular base, and neither the dual abelian scheme nor that identity component \
is available in this library"]
public theorem injective_torsorSectionsRestrictGenericPoint
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (_hreg : IsRegular W)
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG)) :
    Function.Injective (torsorSectionsRestrictGenericPoint B W hW hK G hG F) := by
  by_cases hne : Nonempty (F.1.presheaf.obj (op (Over.mk (𝟙 (B.obj hW)))))
  · obtain ⟨x⟩ := hne
    obtain ⟨φ, hφ⟩ := PseudoTorsor.isTrivial_of_terminal_section Over.mkIdTerminal F.1 x
    have hiso : IsIso φ.hom := hφ
    have hbij : ∀ X, Function.Bijective (φ.hom.app X) :=
      fun X => (isIso_iff_bijective _).mp inferInstance
    have hnat : ∀ y, torsorSectionsRestrictGenericPoint B W hW hK G hG F
          (φ.hom.app (op (Over.mk (𝟙 (B.obj hW)))) y) =
        φ.hom.app (op (genericPointObj B W hW hK))
          (torsorSectionsRestrictGenericPoint B W hW hK G hG
            ⟨trivialTorsor _, trivialTorsor_isTorsor _⟩ y) :=
      fun y => (NatTrans.naturality_apply φ.hom (genericPointToBase B W hW hK).op y).symm
    intro a b hab
    obtain ⟨a', rfl⟩ := (hbij _).surjective a
    obtain ⟨b', rfl⟩ := (hbij _).surjective b
    rw [hnat a', hnat b'] at hab
    exact congrArg _ (injective_torsorSectionsRestrictGenericPoint_trivialTorsor
      B W hW hK G hG ((hbij _).injective hab))
  · exact fun a _ _ => absurd ⟨a⟩ hne

/-- **Stacks 0H8E, part (1).** Let `W` be a regular integral Noetherian scheme with function
field `K` and let `G → W` be an abelian scheme. If the restriction map `P(W) → P(K)` on sections
is surjective for every fppf `G`-torsor `P`, then it is bijective for every such `P`.

Only surjectivity is assumed; injectivity is
`AlgebraicGeometry.injective_torsorSectionsRestrictGenericPoint`. -/
public theorem bijective_torsorSectionsRestrictGenericPoint_of_surjective
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (hreg : IsRegular W)
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    (hsurj : ∀ F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG),
      Function.Surjective (torsorSectionsRestrictGenericPoint B W hW hK G hG F))
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG)) :
    Function.Bijective (torsorSectionsRestrictGenericPoint B W hW hK G hG F) :=
  ⟨injective_torsorSectionsRestrictGenericPoint B W hW hreg hK G hG F, hsurj F⟩

/-- **Stacks 0H8E, part (2).** Let `W` be a regular integral Noetherian scheme with function
field `K` and let `G → W` be an abelian scheme. Then the restriction map
`H¹_fppf(W, G) → H¹_fppf(Spec K, G)` on first cohomology is injective. No hypothesis on the
dimension of `W` enters.

A class in the kernel of the restriction map is the class of a torsor having a section over
`Spec K`, and such a torsor is trivial by the hypothesis `htrivial`, so the class is zero. -/
@[stacks 0H8E "part (2): the conclusion of Stacks 0AF9 with its two-dimensionality hypothesis \
dropped, which is what the tag asserts; the hypotheses on W are exactly noetherian, regular \
and integral. As in Stacks 0AF9 the geometric content is the hypothesis htrivial, that a \
G-torsor with a section over Spec K is trivial. The tag derives part (2) from its part (1), \
the bijectivity of P(W) → P(K): the injectivity half of part (1) is proved here, in \
injective_torsorSectionsRestrictGenericPoint, and its surjectivity half -- the statement that \
the schematic closure of a rational section of P → W is a section, which supplies htrivial by \
fppfH1_restriction_genericPoint_injective_of_surjective_sections -- is not, the tag obtaining \
it by identifying G with the identity component of the Picard scheme of the dual abelian \
scheme and extending a generically defined invertible sheaf over the regular base, and \
neither the dual abelian scheme nor that identity component is available in this library. \
The tag's further remarks, that regularity may be weakened to local factoriality of smooth \
W-schemes and the attribution of the argument, carry no assertion"]
public theorem fppfH1_restriction_genericPoint_injective_of_isTrivial
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (_hreg : IsRegular W)
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    [HasSheafify (BigFppfOver.topology B W hW) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B W hW) AddCommGrpCat.{u})]
    (htrivial : ∀ F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG),
      Nonempty (F.1.presheaf.obj (op (genericPointObj B W hW hK))) → F.1.IsTrivial) :
    Function.Injective (((pointsSheaf B W hW G hG).cohomologyPresheaf 1).map
      (genericPointToBase B W hW hK).op) :=
  Stacks.Cohomology.Torsors.injective_cohomologyPresheaf_map_of_isTrivial
    (pointsSheaf B W hW G hG) Over.mkIdTerminal (genericPointToBase B W hW hK) htrivial

/-- **Part (2) of Stacks 0H8E along the route the tag takes through its part (1).** If the
restriction map `P(W) → P(K)` on sections is surjective for every fppf `G`-torsor `P`, then
the restriction map `H¹_fppf(W, G) → H¹_fppf(Spec K, G)` on first cohomology is injective.

Surjectivity on sections turns a section over `Spec K` into a section over `W`, which makes the
torsor trivial, so it supplies the hypothesis of
`AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_isTrivial`. -/
public theorem fppfH1_restriction_genericPoint_injective_of_surjective_sections
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (hreg : IsRegular W)
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    [HasSheafify (BigFppfOver.topology B W hW) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B W hW) AddCommGrpCat.{u})]
    (hsurj : ∀ F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG),
      Function.Surjective (torsorSectionsRestrictGenericPoint B W hW hK G hG F)) :
    Function.Injective (((pointsSheaf B W hW G hG).cohomologyPresheaf 1).map
      (genericPointToBase B W hW hK).op) :=
  fppfH1_restriction_genericPoint_injective_of_isTrivial B W hW hreg hK G hG
    fun F hne => isTrivial_of_nonempty_sections_genericPoint_of_surjective
      B W hW hK G hG F (hsurj F) hne

end AlgebraicGeometry

end
