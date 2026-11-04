module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCocycle.Transpose

/-!
# The trivialisation of the open domain is a restriction along an equality of opens

Let `ι : D ⟶ X` be an open immersion with a section `p : X ⟶ D`, so `p ≫ ι = 𝟙 X`, and let `N` be
a sheaf of modules on `X`. The trivialisation
`Stacks.AlgebraicGeometry.ProjTwistCocycle.twistTrivialisation` is a morphism from the restriction
of `N` along `ι` to its pushforward along `p`, and both of those have, over an open `T` of `D`,
concrete sections: those of `N` over `ι ''ᵁ T` and over `p ⁻¹ᵁ T` respectively. Since a section of
an open immersion inverts it on opens — `p ⁻¹ᵁ T = ι ''ᵁ T`, which is
`Stacks.AlgebraicGeometry.ProjTwistCocycle.preimage_eq_image` — the two agree, and this file proves
that the trivialisation is the restriction map along that equality and nothing else.

That is the last statement standing between the transposed form of the third assertion of Stacks
Tag 01MZ and a pointwise computation: granted it, every factor of
`Stacks.AlgebraicGeometry.ProjTwistCocycle.twistTranspose` is a presheaf restriction map, so the
transposed cocycle acts on the underlying homogeneous fractions by reindexing and its content is
`Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp`.

## Main results

* `…ProjTwistCocycle.twistTrivialisation_app`: **the trivialisation on sections over an arbitrary
  open of `D` is the restriction along `p ⁻¹ᵁ T = ι ''ᵁ T`.**
* `…ProjTwistCocycle.twistTrivialisation_val_app_apply`: the same statement read on a section,
  which is the form the pointwise cocycle consumes.

## Implementation notes

`Stacks.AlgebraicGeometry.ProjTwistCocycle.twistTrivialisation_app_preimage` already pins the
trivialisation at the opens of the form `ι ⁻¹ᵁ W` for an open `W` of `X`. Every open of `D` is of
that form, `T = ι ⁻¹ᵁ (ι ''ᵁ T)` for an open immersion, but only propositionally, and that equality
sits inside the *argument type* of the section map: `rw` cannot abstract it, the motive being
dependent, and `obtain rfl` cannot substitute it, the right-hand side being the variable that the
left-hand side mentions. So the transport is not a rewrite.

It is instead **naturality**, which moves between two opens without identifying them. Applied to
`eqToHom (ι.preimage_image_eq T).symm : T ⟶ ι ⁻¹ᵁ (ι ''ᵁ T)` it expresses the trivialisation at `T`
in terms of the trivialisation at `ι ⁻¹ᵁ (ι ''ᵁ T)`, where the characterisation is available. The
restriction that naturality introduces on the source is inverted not by constructing an inverse but
by composing with the restriction that the unit of the restriction adjunction already is: the two
are mutually inverse because their composite is a restriction from an open to itself, hence the
identity. No step of the proof crosses the conversion between `(p ≫ ι)_*` and `ι_* p_*`; it is
crossed once, in the statement of `twistTrivialisation_app_preimage`.

Morphisms between opens of a scheme are unique, so a restriction map of `N` depends only on its two
opens; `presheaf_map_subsingleton` is that remark, and it is what identifies each composite of
restrictions appearing in the proof with the single restriction it must be. Composites of
restrictions are contracted with `CategoryTheory.Functor.map_comp` applied by `Eq.trans` rather
than by `rw`, which does not see through the identification of the sections of a restriction or of
a pushforward with sections of `N`.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ProjTwistCocycle

universe u

section Trivialisation

variable {X D : Scheme.{u}} (p : X ⟶ D) (ι : D ⟶ X) (hpi : p ≫ ι = 𝟙 X) (N : X.Modules)
  [IsOpenImmersion ι]

/-- **A restriction map of a sheaf of modules depends only on its two opens.** The opens of a
scheme form a partial order, so there is at most one morphism between two of them. -/
public theorem presheaf_map_subsingleton {U V : X.Opens} (f g : op V ⟶ op U) :
    N.presheaf.map f = N.presheaf.map g :=
  congrArg N.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- A composite of restriction maps of `N` is the restriction map between the outer opens. -/
private theorem presheaf_map_comp_eq {U V W : X.Opens} (f : op V ⟶ op U) (g : op U ⟶ op W)
    (h : op V ⟶ op W) : N.presheaf.map f ≫ N.presheaf.map g = N.presheaf.map h :=
  (Functor.map_comp N.presheaf f g).symm.trans (presheaf_map_subsingleton N _ _)

/-- **The trivialisation of the open domain is the restriction along `p ⁻¹ᵁ T = ι ''ᵁ T`.** Over an
open `T` of `D` the restriction of `N` along `ι` has the sections of `N` over `ι ''ᵁ T` and the
pushforward of `N` along `p` has those over `p ⁻¹ᵁ T`; a section of an open immersion inverts it on
opens, and the trivialisation is the resulting restriction map and nothing else.

`twistTrivialisation_app_preimage` is this statement at the opens of the form `ι ⁻¹ᵁ W`, and the
transport to an arbitrary `T` is naturality at
`eqToHom (ι.preimage_image_eq T).symm : T ⟶ ι ⁻¹ᵁ (ι ''ᵁ T)` together with the fact that the
restriction the unit of the restriction adjunction is, and the one naturality introduces, are
mutually inverse. -/
public theorem twistTrivialisation_app (T : D.Opens) :
    (twistTrivialisation p ι hpi N).app T =
      N.presheaf.map (eqToHom (preimage_eq_image p ι hpi T)).op := by
  have hnat := (twistTrivialisation p ι hpi N).mapPresheaf.naturality
    (eqToHom (ι.preimage_image_eq T).symm).op
  simp only [Scheme.Modules.mapPresheaf_app] at hnat
  have hpre := twistTrivialisation_app_preimage p ι hpi N (ι ''ᵁ T)
  have hid : N.presheaf.map (homOfLE (ι.image_preimage_le (ι ''ᵁ T))).op ≫
      ((Scheme.Modules.restrictFunctor ι).obj N).presheaf.map
        (eqToHom (ι.preimage_image_eq T).symm).op = 𝟙 _ := by
    exact (presheaf_map_comp_eq N _ _ (𝟙 _)).trans (N.presheaf.map_id _)
  refine Eq.trans (Category.id_comp _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ (twistTrivialisation p ι hpi N).app T) hid).symm ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => N.presheaf.map
    (homOfLE (ι.image_preimage_le (ι ''ᵁ T))).op ≫ z) hnat) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ ((Scheme.Modules.pushforward p).obj N).presheaf.map
    (eqToHom (ι.preimage_image_eq T).symm).op) hpre) ?_
  rw [Scheme.Modules.pushforwardCongr_inv_app_app,
    Scheme.Modules.pushforward_obj_presheaf_map]
  exact presheaf_map_comp_eq N _ _ _

/-- **The trivialisation of the open domain, read on a section.** `twistTrivialisation_app` applied
to a section `y` of `N` over `ι ''ᵁ T`, which is the form in which the factors of
`Stacks.AlgebraicGeometry.ProjTwistCocycle.twistTranspose` are compared on underlying homogeneous
fractions. -/
public theorem twistTrivialisation_val_app_apply (T : D.Opens)
    (y : ((Scheme.Modules.restrictFunctor ι).obj N).val.obj (op T)) :
    (twistTrivialisation p ι hpi N).val.app (op T) y =
      N.val.map (eqToHom (preimage_eq_image p ι hpi T)).op y :=
  congr($(twistTrivialisation_app p ι hpi N T) y)

end Trivialisation

end Stacks.AlgebraicGeometry.ProjTwistCocycle

end
