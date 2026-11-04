module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartMonoReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization

/-!
# Transporting the comparison map of Stacks 04CX along maps of differentials

Let

```
X' --f--> X
|         |
p'        p
v         v
Y' --q--> Y
```

be a commutative square of algebraic spaces over a scheme `S`.  Stacks 04CX characterizes the
comparison map `c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` by the behaviour of its adjoint transpose on
universal differentials, `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`.  This file records
how that characterizing property transports along a morphism of modules composed on either side,
and applies the result to the **étale-base step of Stacks 04CU for the comparison map**.

## Main results

* `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.map_comp`: a morphism
  `j : Ω_{X/Y} ⟶ Ω_{X/Y₁}` carrying universal differentials to universal differentials turns a
  comparison map of the square with left edge `p₁` into one of the square with left edge `p`,
  after pulling `j` back along `f`.
* `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.comp_right`: dually, composing a comparison
  map with a morphism `k : Ω_{X'/Y'} ⟶ Ω_{X'/Y''}` carrying universal differentials to universal
  differentials gives a comparison map for the square with right-hand lower corner `Y''`.
* `AlgebraicGeometry.Space.universalDerivation_sharpIsoInv`: the backward comparison of the
  étale-base step of Stacks 04CU carries one universal derivation to the other, the companion of
  `AlgebraicGeometry.Space.universalDerivation_sheafOfDifferentialsIsoOfSharpIso`.
* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleBase`: **Stacks 04CU, the étale-base
  step for the comparison map of Stacks 04CX.**  For `ψ : U ⟶ V` over `q : V ⟶ W` and an étale
  `cw : W ⟶ Z`, the comparison map `c_ψ : ψ^*Ω_{V/W} ⟶ Ω_{U/W}` over `W`, read through the
  étale-base identifications `Ω_{V/W} ≅ Ω_{V/Z}` and `Ω_{U/W} ≅ Ω_{U/Z}`, is the comparison map
  of the same square over `Z`.  `sheafOfDifferentialsIsoOfSharpIso` identifies those objects;
  this is the compatibility with the *map* that identification was missing.
* `AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_of_etaleBase`: consequently monomorphy
  of the first map of the transitivity sequence of Stacks 05Z8 is unchanged when the base is
  replaced by an algebraic space it is étale over.

## Implementation notes

Both transport lemmas are proved from the naturality of the hom-set bijection of
`f^* ⊣ f_*` of Stacks 03LU in one of its two arguments.  Naturality in the left argument needs
nothing else.  Naturality in the right argument leaves the direct image
`f_*k : f_*Ω_{X'/Y'} ⟶ f_*Ω_{X'/Y''}` applied to the derivation of Stacks 04CX, and that is
computed in `AlgebraicGeometry.Space.modulePushforward_map_pushforwardUniversalDerivationHom`
*on sections*: the identity it comes from is an identity of morphisms of sheaves of sets, where
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map` is a definitional
equality, so no comparison of the two spellings of the direct image of modules occurs.

## References

* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 05Z8](https://stacks.math.columbia.edu/tag/05Z8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y Z Y' Y'' X' : AlgebraicSpaces B S hS}

/-! ### Transporting the characterizing property of Stacks 04CX -/

/-- **A morphism out of `Ω_{X/Y}` pulled back along `f` composes with a morphism into
`Ω_{X'/Y'}` to a comparison map of Stacks 04CX** as soon as the adjoint transpose of the second
factor carries the image under the first factor of the universal differential of a local section
to the derivation of Stacks 04CX.

This is naturality of the hom-set bijection of `f^* ⊣ f_*` in its left argument, and nothing
else: the transpose of `f^*j ≫ r` is `j` followed by the transpose of `r`. -/
theorem isSheafOfDifferentialsMap_map_comp (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    {M : Modules.{u, u} B S hS X.1 X.2}
    (j : sheafOfDifferentials B S hS p ⟶ M)
    (r : (modulePullback B S hS f).obj M ⟶ sheafOfDifferentials B S hS p')
    (h : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U),
      (((modulePullbackAdjunction B S hS f).homEquiv M
          (sheafOfDifferentials B S hS p') r).val.app U).hom
          ((j.val.app U).hom ((universalDerivation B S hS p).d t)) =
        (pushforwardUniversalDerivationHom B S hS f p').hom.app U t) :
    IsSheafOfDifferentialsMap B S hS f p p' ((modulePullback B S hS f).map j ≫ r) := by
  intro U t
  rw [Adjunction.homEquiv_naturality_left]
  exact h U t

/-- **The direct image of a morphism carrying universal differentials to universal differentials
carries the derivation of Stacks 04CX for one left edge to the one for another**, on local
sections.

The underlying identity is between morphisms of sheaves of *sets*: the derivation of Stacks 04CX
is the structure map of `f` followed by the direct image of `d_{X'/Y'}` by
`AlgebraicGeometry.Space.pushforwardUniversalDerivationHom_eq`, the direct image of modules is
the direct image of sheaves of sets on underlying sheaves by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map`, and the hypothesis says
exactly that `d_{X'/Y'}` followed by `k` is `d_{X'/Y''}`. -/
theorem modulePushforward_map_pushforwardUniversalDerivationHom (f : X' ⟶ X) (p' : X' ⟶ Y')
    (p'' : X' ⟶ Y'')
    (k : sheafOfDifferentials B S hS p' ⟶ sheafOfDifferentials B S hS p'')
    (hk : ∀ (V : (SmallEtale B S hS X'.1)ᵒᵖ) (y : (structureRingSheaf B S hS X').obj.obj V),
      (k.val.app V).hom ((universalDerivation B S hS p').d y) =
        (universalDerivation B S hS p'').d y)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U) :
    (((modulePushforward B S hS f).map k).val.app U).hom
        ((pushforwardUniversalDerivationHom B S hS f p').hom.app U t) =
      (pushforwardUniversalDerivationHom B S hS f p'').hom.app U t := by
  have hd : universalDerivationHom B S hS p' ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k =
      universalDerivationHom B S hS p'' :=
    CategoryTheory.Sheaf.hom_ext_sections fun V y => hk V y
  have key : pushforwardUniversalDerivationHom B S hS f p' ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePushforward B S hS f).map k) =
      pushforwardUniversalDerivationHom B S hS f p'' := by
    rw [pushforwardUniversalDerivationHom_eq, pushforwardUniversalDerivationHom_eq,
      moduleSheafFunctor_map_modulePushforward_map]
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun m => structureSharpSet B S hS f ≫ m) ?_
    refine Eq.trans ((smallEtaleDirectImage B S hS f).map_comp _ _).symm ?_
    exact congrArg (smallEtaleDirectImage B S hS f).map hd
  exact Sheaf.sections_congr key U t

/-- **A comparison map of Stacks 04CX composed with a morphism carrying universal differentials
to universal differentials is again a comparison map of Stacks 04CX**, for the square whose
left edge is the second one.

Naturality of the hom-set bijection of `f^* ⊣ f_*` in its right argument turns the transpose of
`c ≫ k` into the transpose of `c` followed by the direct image of `k`, and
`AlgebraicGeometry.Space.modulePushforward_map_pushforwardUniversalDerivationHom` evaluates
that. -/
theorem IsSheafOfDifferentialsMap.comp_right (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (p'' : X' ⟶ Y'')
    {c : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS f p p' c)
    (k : sheafOfDifferentials B S hS p' ⟶ sheafOfDifferentials B S hS p'')
    (hk : ∀ (V : (SmallEtale B S hS X'.1)ᵒᵖ) (y : (structureRingSheaf B S hS X').obj.obj V),
      (k.val.app V).hom ((universalDerivation B S hS p').d y) =
        (universalDerivation B S hS p'').d y) :
    IsSheafOfDifferentialsMap B S hS f p p'' (c ≫ k) := by
  intro U t
  rw [Adjunction.homEquiv_naturality_right]
  refine Eq.trans ?_ (modulePushforward_map_pushforwardUniversalDerivationHom
    B S hS f p' p'' k hk U t)
  exact congrArg (((modulePushforward B S hS f).map k).val.app U).hom (hc U t)

/-- **A comparison map of Stacks 04CX precomposed with the pullback of a morphism carrying
universal differentials to universal differentials is again a comparison map of Stacks 04CX**,
for the square whose right edge is the first one.  This is the companion of
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.comp_right` on the other side. -/
theorem IsSheafOfDifferentialsMap.map_comp (f : X' ⟶ X) (p : X ⟶ Y)
    {Y₁ : AlgebraicSpaces B S hS} (p₁ : X ⟶ Y₁) (p' : X' ⟶ Y')
    {r : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p₁) ⟶
      sheafOfDifferentials B S hS p'}
    (hr : IsSheafOfDifferentialsMap B S hS f p₁ p' r)
    (j : sheafOfDifferentials B S hS p ⟶ sheafOfDifferentials B S hS p₁)
    (hj : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U),
      (j.val.app U).hom ((universalDerivation B S hS p).d t) =
        (universalDerivation B S hS p₁).d t) :
    IsSheafOfDifferentialsMap B S hS f p p' ((modulePullback B S hS f).map j ≫ r) :=
  isSheafOfDifferentialsMap_map_comp B S hS f p p' j r
    (fun U t => by rw [hj U t]; exact hr U t)

/-! ### The étale-base step of Stacks 04CU for the comparison map -/

/-- **The backward comparison of the étale-base step of Stacks 04CU carries one universal
derivation to the other.**  This is the companion of
`AlgebraicGeometry.Space.universalDerivation_sheafOfDifferentialsIsoOfSharpIso` for the inverse
of that identification, and has the same one-line proof: the defining property of
`AlgebraicGeometry.Space.sharpIsoInv` read on a local section. -/
theorem universalDerivation_sharpIsoInv (p : X ⟶ Y) (q : X ⟶ Z)
    (e : inverseImageStructureSheaf B S hS q ≅ inverseImageStructureSheaf B S hS p)
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q)
    {W : (SmallEtale B S hS X.1)ᵒᵖ} (x : (structureRingSheaf B S hS X).obj.obj W) :
    (((sharpIsoInv B S hS p q e he).val.app W).hom)
        ((universalDerivation B S hS q).d x) =
      (universalDerivation B S hS p).d x :=
  PresheafOfModules.Derivation.congr_d
    ((differentialsHomEquiv B S hS q (sheafOfDifferentials B S hS p)).apply_symm_apply
      ((universalDerivation B S hS p).precompBase e.hom.hom
        (sharpFactorHom B S hS p q e he))) x

section EtaleBase

variable {U V W : AlgebraicSpaces B S hS} (ψ : U ⟶ V) (q : V ⟶ W) (cw : W ⟶ Z)
    (hcw : IsEtale B S hS cw.hom)

/-- The étale-base identification `Ω_{V/W} ≅ Ω_{V/Z}` of Stacks 04CU along an étale
`cw : W ⟶ Z`, at the left edge `q : V ⟶ W` of a square. -/
def etaleBaseDifferentialsIso :
    sheafOfDifferentials B S hS q ≅ sheafOfDifferentials B S hS (q ≫ cw) :=
  sheafOfDifferentialsIsoOfSharpIso B S hS q (q ≫ cw)
    (etaleBaseInverseImageStructureSheafIso B S hS q cw hcw)
    (etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage B S hS q cw hcw)

/-- The étale-base identification carries the universal `W`-derivation to the universal
`Z`-derivation of the same local section. -/
theorem universalDerivation_etaleBaseDifferentialsIso_hom
    (T : (SmallEtale B S hS V.1)ᵒᵖ) (x : (structureRingSheaf B S hS V).obj.obj T) :
    (((etaleBaseDifferentialsIso B S hS q cw hcw).hom.val.app T).hom)
        ((universalDerivation B S hS q).d x) =
      (universalDerivation B S hS (q ≫ cw)).d x :=
  universalDerivation_sheafOfDifferentialsIsoOfSharpIso B S hS q (q ≫ cw)
    (etaleBaseInverseImageStructureSheafIso B S hS q cw hcw)
    (etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage B S hS q cw hcw) x

/-- The étale-base identification carries the universal `Z`-derivation back to the universal
`W`-derivation of the same local section. -/
theorem universalDerivation_etaleBaseDifferentialsIso_inv
    (T : (SmallEtale B S hS V.1)ᵒᵖ) (x : (structureRingSheaf B S hS V).obj.obj T) :
    (((etaleBaseDifferentialsIso B S hS q cw hcw).inv.val.app T).hom)
        ((universalDerivation B S hS (q ≫ cw)).d x) =
      (universalDerivation B S hS q).d x :=
  universalDerivation_sharpIsoInv B S hS q (q ≫ cw)
    (etaleBaseInverseImageStructureSheafIso B S hS q cw hcw)
    (etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage B S hS q cw hcw) x

/-- **Stacks 04CU, the étale-base step for the comparison map of Stacks 04CX.**  Let
`ψ : U ⟶ V` be a morphism of algebraic spaces, `q : V ⟶ W` a structure morphism and
`cw : W ⟶ Z` étale.  The comparison map `c_ψ : ψ^*Ω_{V/W} ⟶ Ω_{U/W}` of the square over `W`,
read through the étale-base identifications `Ω_{V/W} ≅ Ω_{V/Z}` of the right edge and
`Ω_{U/W} ≅ Ω_{U/Z}` of the left edge, has the characterizing property of the comparison map of
the same square over `Z`.

`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso` supplies those identifications as
isomorphisms of objects; what makes them compatible with the comparison map is that each carries
one universal derivation to the other, so that
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.map_comp` and
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.comp_right` apply. -/
@[stacks 04CU "the étale-base step for the comparison map of 04CX: the comparison map over `W` \
read through the identifications `Ω_{V/W} ≅ Ω_{V/Z}` and `Ω_{U/W} ≅ Ω_{U/Z}` is the comparison \
map over `Z`"]
theorem isSheafOfDifferentialsMap_etaleBase :
    IsSheafOfDifferentialsMap B S hS ψ (q ≫ cw) ((ψ ≫ q) ≫ cw)
      ((modulePullback B S hS ψ).map (etaleBaseDifferentialsIso B S hS q cw hcw).inv ≫
        pullbackDifferentialsMap B S hS ψ q ≫
          (etaleBaseDifferentialsIso B S hS (ψ ≫ q) cw hcw).hom) :=
  IsSheafOfDifferentialsMap.map_comp B S hS ψ (q ≫ cw) q ((ψ ≫ q) ≫ cw)
    (IsSheafOfDifferentialsMap.comp_right B S hS ψ q (ψ ≫ q) ((ψ ≫ q) ≫ cw)
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS ψ q (ψ ≫ q) (𝟙 W) (by simp))
      (etaleBaseDifferentialsIso B S hS (ψ ≫ q) cw hcw).hom
      (fun T y => universalDerivation_etaleBaseDifferentialsIso_hom B S hS (ψ ≫ q) cw hcw T y))
    (etaleBaseDifferentialsIso B S hS q cw hcw).inv
    (fun T x => universalDerivation_etaleBaseDifferentialsIso_inv B S hS q cw hcw T x)

include hcw in
/-- **Monomorphy of the first map of the transitivity sequence of Stacks 05Z8 is insensitive to
replacing the base by an algebraic space it is étale over.**  For `ψ : U ⟶ V` over `q : V ⟶ W`
and an étale `cw : W ⟶ Z`, the comparison map `c_ψ : ψ^*Ω_{V/Z} ⟶ Ω_{U/Z}` is a monomorphism as
soon as `c_ψ : ψ^*Ω_{V/W} ⟶ Ω_{U/W}` is.

By `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleBase` and the uniqueness clause of
Stacks 04CX the former *is* the latter, composed on both sides with the étale-base
identifications of Stacks 04CU and the transport along the associativity of the left edge. -/
theorem mono_pullbackDifferentialsMap_of_etaleBase
    (h : Mono (pullbackDifferentialsMap B S hS ψ q)) :
    Mono (pullbackDifferentialsMap B S hS ψ (q ≫ cw)) := by
  have hc := IsSheafOfDifferentialsMap.congr_right B S hS
    (isSheafOfDifferentialsMap_etaleBase B S hS ψ q cw hcw) (Category.assoc ψ q cw)
  have hbase : IsSheafOfDifferentialsMap B S hS ψ (q ≫ cw) (ψ ≫ q ≫ cw)
      (pullbackDifferentialsMap B S hS ψ (q ≫ cw)) :=
    isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS ψ (q ≫ cw) (ψ ≫ q ≫ cw) (𝟙 Z)
      (by simp)
  rw [eq_of_isSheafOfDifferentialsMap B S hS ψ (q ≫ cw) (ψ ≫ q ≫ cw) hbase hc]
  have := h
  infer_instance

end EtaleBase

end AlgebraicGeometry.Space

end
