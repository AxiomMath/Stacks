module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleEtaleRestrictionCanonical

/-!
# The composition law of Stacks 04CO with its two composites supplied as data

`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_comp` states the composition
law of [Stacks Project, Tag 04CO] at the two composites `g ≫ g'` of étale morphisms and `f ≫ f'`
of morphisms of subspaces.  This file states the law at arbitrary morphisms `gc` and `fc` equal
to these composites, with the two factorizations and the resulting change of the inverse image
as hypotheses.

## Main results

* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_hom_comp_of_factorizations`:
  **the composition law of [Stacks Project, Tag 04CO] at an arbitrary spelling of each of its two
  composites.**

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X X₂ X₃ : AlgebraicSpaces B S hS}

/-- **The composition law of [Stacks Project, Tag 04CO] at an arbitrary spelling of each of its
two composites.**  Let

```
Zc  --f--> Z'  --f'--> Z''
|          |           |
X   --g--> X₂  --g'--> X₃
```

be two cartesian squares with `g` and `g'` étale, let `gc` be any spelling of `g ≫ g'` and `fc`
any spelling of `f ≫ f'`.  Then the identification of [Stacks Project, Tag 04CO] at `gc` and `fc`
is the change of the inverse image along the two spellings of `fc`, followed by the composition
comparison of [Stacks Project, Tag 03LU], followed by the inverse image along `f` of the
identification for `g'`, followed by the identification for `g`. -/
theorem conormalModuleEtaleRestrictionCanonicalIso_hom_comp_of_factorizations
    (Zc : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X₂.1)
    (Z'' : ClosedSubspaces B S hS X₃.1)
    (g : X ⟶ X₂) (g' : X₂ ⟶ X₃) (gc : X ⟶ X₃) (hgc : g ≫ g' = gc)
    (f : (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (f' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (fc : (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hfc : f ≫ f' = fc)
    (hsq : subspaceInclusion B S hS X Zc ≫ g = f ≫ subspaceInclusion B S hS X₂ Z')
    (hsq' : subspaceInclusion B S hS X₂ Z' ≫ g' = f' ≫ subspaceInclusion B S hS X₃ Z'')
    (hcart : IsPullback Zc.1.ι f.hom g.hom Z'.1.ι)
    (hcart' : IsPullback Z'.1.ι f'.hom g'.hom Z''.1.ι)
    (hg : IsEtale B S hS g.hom) (hg' : IsEtale B S hS g'.hom)
    (hsqc : subspaceInclusion B S hS X Zc ≫ gc = fc ≫ subspaceInclusion B S hS X₃ Z'')
    (hcartc : IsPullback Zc.1.ι fc.hom gc.hom Z''.1.ι)
    (hgc' : IsEtale B S hS gc.hom)
    (e : (modulePullback B S hS fc).obj (conormalModule B S hS X₃ Z'') =
      (modulePullback B S hS (f ≫ f')).obj (conormalModule B S hS X₃ Z'')) :
    (conormalModuleEtaleRestrictionCanonicalIso B S hS Zc Z'' gc fc hsqc hcartc hgc').hom =
      eqToHom e ≫
        (modulePullbackCompIso B S hS f f').inv.app (conormalModule B S hS X₃ Z'') ≫
          (modulePullback B S hS f).map
              (conormalModuleEtaleRestrictionCanonicalIso B S hS Z' Z'' g' f'
                hsq' hcart' hg').hom ≫
            (conormalModuleEtaleRestrictionCanonicalIso B S hS Zc Z' g f hsq hcart hg).hom := by
  subst hgc
  subst hfc
  rw [eqToHom_refl, Category.id_comp]
  exact conormalModuleEtaleRestrictionCanonicalIso_comp B S hS Zc Z' Z'' g g' f f'
    hsq hsq' hcart hcart' hg hg'

end AlgebraicGeometry.Space

end
